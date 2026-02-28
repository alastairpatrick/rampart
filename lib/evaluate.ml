open Ast
open Effect
open Effect.Deep
open Error
open Location
open Slot
open Type
open Value

exception Return_exn of value

type _ Effect.t +=
| Fork : (unit -> unit) -> unit t
| Defer : (string * assignable) -> unit t

type machine = {
  globals: variable array;
}

type frame = {
  depth: int;
  enclosing_frame: frame option;
  variables: variable array;
  return_type: typ;
  pure: bool;
}

type thread = {
  top_frame: frame;
}

type implementation_value +=
  | ImplLambda of frame * statement
  | ImplRepresentative

type result_mode =
  | EvalFull        (* Evaluate result of expression fully with all side effects. Both result value and type must be correct. *)
  | EvalTypeOnly    (* Only the type of the result need be correct. Use this to determine type of expression without causing side effects. *)

let fork f = perform (Fork f)
let defer pattern assignable = perform (Defer (pattern, assignable))

let make_thread (machine : machine) : thread = {
  top_frame = {
    depth = 0;
    enclosing_frame = None;
    variables = machine.globals;
    return_type = void_type;
    pure = false;
  };
}

let make_machine (num_globals : int) : machine = {
  globals = Array.make num_globals empty_variable;
}

let rec convert_implicit (value : value) (to_typ : typ) : value =
  let from_typ = type_of_value value in
  match to_typ, value with
  | _ when to_typ = from_typ -> value

  (* Purity is a covariant property of function types, i.e. a pure function can be used in place of an impure function but not vice versa, since purity of the callee is part of the contract that the caller relies on. However, if the source type is already pure then we can allow it to be converted to an impure type since it will still uphold the contract. *)
  | Singleton Function (to_return_type, to_param_types, to_pure), Impl (Singleton (Function (from_return_type, from_param_types, from_pure)), impl)
    when (to_return_type, to_param_types) = (from_return_type, from_param_types) ->
      if (from_pure = to_pure) || from_pure then
        Impl (Singleton (Function (from_return_type, from_param_types, to_pure)), impl)
      else
        raise (error_implicit_conversion from_typ to_typ)

  (* Tuples of type values can be implicitly converted to singleton type values of tuple type *)
  | Singleton Type, _ ->
    (try
      Type (value_to_type value)
    with Error _ -> raise error_type_mismatch)

  | Tuple to_element_types, Tuple from_elements ->
    assert (Iarray.length to_element_types <> 1);
    assert (Array.length from_elements <> 1); (* otherwise these would use the explicit singleton representaion *)
    if (Iarray.length to_element_types <> Array.length from_elements) then raise error_type_mismatch;
    Tuple (Array.init (Array.length from_elements) (fun i -> convert_implicit from_elements.(i) (Iarray.get to_element_types i)))

  | Tuple to_element_types, Type (Tuple from_element_types) ->
    assert (Iarray.length to_element_types <> 1);
    assert (Iarray.length from_element_types <> 1);
    if (Iarray.length to_element_types <> Iarray.length from_element_types) then raise error_type_mismatch;
    (* This branch allows destructuring a value of tuple type into a tuple value. TODO: not sure if we actually want to do this. *)
    Tuple (Array.init (Iarray.length from_element_types) (fun i -> convert_implicit (Type (Iarray.get from_element_types i)) (Iarray.get to_element_types i)))

  | _ -> raise (error_implicit_conversion from_typ to_typ)

let rec representative_value_for_type (typ : typ) : value =
  match typ with
  | Singleton Int
  | Singleton Bool
  | Tuple [| |] ->
    default_value typ
  | Singleton Type ->
    Type (Singleton Type)
  | Singleton singleton_type ->
    Impl (Singleton singleton_type, ImplRepresentative)
  | Tuple types ->
    tuple_value (Seq.map representative_value_for_type (Iarray.to_seq types))

let rec get_assignable frame {index; depth} : assignable =
  if depth = frame.depth then
    index, frame.variables
  else
    get_assignable (Option.get frame.enclosing_frame) {index; depth}

and set_assignable_value (index, variable_array) value : unit =
  match value with
  | Uninitialized None | Assignable _ -> assert false
  | _ -> variable_array.(index) <- { variable_array.(index) with value }

and set_assignable_modifiers (index, variable_array) modifiers : unit =
  variable_array.(index) <- { variable_array.(index) with modifiers }
  
and get_assignable_value (index, variable_array) : value =
  match variable_array.(index).value with
  | Failed -> raise Saw_failed_error
  | value -> value

and get_assignable_modifiers (index, variable_array) : variable_modifiers =
  variable_array.(index).modifiers

(* strip_assignability resolves `Assignable` wrappers to their stored contents.
   Behavior and deferral semantics:
   - If the slot contains a value, return its contents.
   - If the slot is `Uninitialized` and we are evaluating for value/side-effects
     (`EvalFull`), perform a `Defer` effect with the slot's display name and
     assignable. The `Defer` effect is handled by `evaluate_to_completion`, which
     suspends the current continuation and enqueues it with a dependency on the
     named slot. When the dependency is satisfied (the slot becomes initialized
     or failed), the continuation is resumed. After performing `defer` we read
     the slot via `get_assignable_value` rather than recursively calling
     `strip_assignability` to avoid immediately re-performing the effect and
     causing an infinite loop.
   - If we are evaluating only for a type (`EvalTypeOnly`) and the slot is
     `Uninitialized (Some typ)`, synthesize a representative value for that
     type (via `representative_value_for_type`) to allow `typeof` and similar
     operations to break dependency cycles without causing side effects.
*)
and strip_assignability (mode : result_mode) (value : value) : value =
  match value with
  | Assignable (assignable, display_name) ->
    let contents = get_assignable_value assignable in
    (match mode, contents with
    | EvalTypeOnly, Uninitialized (Some typ) ->
        representative_value_for_type typ
    | _, Uninitialized _ ->
      defer display_name assignable;
      get_assignable_value assignable
    | _ -> contents)
  | Tuple elements ->
    Tuple (Array.map (strip_assignability mode) elements)
  | _ -> value

and evaluate_unassignable thread mode expression : value = strip_assignability mode (evaluate thread mode expression)

and evaluate_binary_op thread mode _ op a b : value =
  let a = evaluate_unassignable thread mode a in
  let b = evaluate_unassignable thread mode b in
  match op, a, b with
  | Plus, Int a, Int b -> Int (a+b)
  | Div, Int a, Int b -> (match mode, b with
    | EvalTypeOnly, 0 -> representative_value_for_type (Singleton Int)
    | _ -> Int (a/b))
  | _ -> raise (error_invalid_operation (Printf.sprintf "unsupported binary '%s' operation for types '%s' and '%s'"
    (show_binary_op op) (show_typ (type_of_value a)) (show_typ (type_of_value b))))

and evaluate_typeof thread _ expression : value =
  type_to_value (type_of_value (evaluate_unassignable thread EvalTypeOnly expression))

and evaluate_arity thread mode expression : value =
  match evaluate_unassignable thread mode expression with
  | Tuple values -> Int (Array.length values)
  | _ -> Int 1

and evaluate_assignment thread mode _ a b : value =
  let b = evaluate_unassignable thread mode b in
  let rec assign (a : expression) (b : value) : value =
    (match a, b with
    | (_, BoundIdentifier (display_name, slot)), _ ->
      let assignable = get_assignable thread.top_frame slot in
      if not (get_assignable_modifiers assignable).mut then raise (error_immutable_assignment display_name);
      (* Should not attempt to assign LHS until after it has been initialized. *)
      (match (get_assignable_value assignable) with
        | Uninitialized _ -> defer display_name assignable
        | _ -> ());
      let typ = type_of_value (get_assignable_value assignable) in
      let converted_b = convert_implicit b typ in
      if mode <> EvalTypeOnly then set_assignable_value assignable converted_b;
      converted_b
    | (_, BoundLet (_, slot)), _ ->
      let assignable = get_assignable thread.top_frame slot in
      if mode <> EvalTypeOnly then set_assignable_value assignable b;
      b
    | (_, Tuple exprs), Tuple values ->
      assert (Array.length values <> 1); (* otherwise these would use the explicit singleton representaion *)
      if (List.length exprs <> Array.length values) then raise error_type_mismatch;
      let result = Array.make (Array.length values) (Uninitialized None) in
      List.iteri (fun i expr -> result.(i) <- assign expr values.(i)) exprs;
      Tuple (result)
    | (_, Tuple _), _ -> raise error_type_mismatch
    | (location, _), _ -> raise (error_not_assignable location)) in
  assign a b

and evaluate_in thread mode _ a b : value =
  ignore (evaluate_unassignable thread mode a);
  evaluate_unassignable thread mode b

and evaluate_lambda thread mode return_type (params : statement Seq.t) (modifiers : lambda_modifiers) body : value =
  let return_type = evaluate_unassignable thread mode return_type |> value_to_type in
  let param_types = Iarray.of_seq (Seq.map (fun (location, stmt) ->
    match stmt with
    | BoundDeclaration ({ type_expr=Some type_expr; _ }, _) ->
      evaluate_unassignable thread mode type_expr |> value_to_type
    | _ -> print_endline (show_statement (location, stmt)); assert false) params) in
  Impl ( Singleton (Function (return_type, param_types, modifiers.pure)),
    ImplLambda (thread.top_frame, body))

and evaluate_call thread mode _ callee (args : expression Seq.t) pure : value =
  let callee = evaluate_unassignable thread mode callee in
  match callee with
  | Impl (Singleton (Function (return_type, param_types, pure)), ImplLambda (enclosing_frame, (_, BoundFrame (num_locals, body)))) ->
    if not pure && thread.top_frame.pure then raise error_purity_mismatch;
    if mode = EvalTypeOnly then
      representative_value_for_type return_type
    else
      let callee_thread = {
        top_frame = {
          depth = enclosing_frame.depth + 1;
          enclosing_frame = Some enclosing_frame;
          variables = Array.make num_locals empty_variable;
          return_type = return_type;
          pure = pure;
        }
      } in
      let rec evaluate_args i (args: expression Seq.t) : unit =
        match Seq.uncons args with
        | None ->
          if i <> Iarray.length param_types then raise error_type_mismatch
        | Some (arg, arg_rest) ->
            let value = evaluate_unassignable thread mode arg in
            let converted_value = convert_implicit value (Iarray.get param_types i) in
            callee_thread.top_frame.variables.(i) <- { callee_thread.top_frame.variables.(i) with value = converted_value };
            evaluate_args (i+1) arg_rest in
      evaluate_args 0 args;
      (try
        evaluate_order_dependent callee_thread (List.to_seq body);
        (* If the function falls off the end without a return, produce the default value for the
        declared return type. This matches variable initialization behaviour and avoids
        silently returning `void` for non-void functions. *)
        default_value return_type
      with Return_exn value ->
      let from_typ = type_of_value value in
      if from_typ = return_type then value else raise (error_implicit_conversion from_typ return_type))

  (* Syntactically, a function type parses the same way as a function call, i.e. a(b) could be a call to a with argument b
  if a is a function typed value or a function type value, returning type a and taking an argument of type b, if a is a type. *)
  | _ ->
    try
      let return_type = value_to_type callee in
      let param_types = Iarray.of_seq (Seq.map (fun arg -> value_to_type (evaluate_unassignable thread mode arg)) args) in
      Type (Singleton (Function (return_type, param_types, pure)))
    with Error _ -> raise error_not_callable
    

and evaluate (thread : thread) (mode : result_mode) ((location, expression) : expression) : value =
  try
    match expression with
    | IntLiteral l -> Int l
    | BoolLiteral b -> Bool b
    | Type Int -> Type (Singleton Int)
    | Type Bool -> Type (Singleton Bool)
    | Type Void -> void
    | Type Type -> Type (Singleton Type)
    | BinaryOp (op, a, b) -> evaluate_binary_op thread mode location op a b
    | Tuple exprs -> tuple_value (Seq.map (evaluate thread mode) (List.to_seq exprs))
    | TypeOf e -> evaluate_typeof thread mode e
    | Arity e -> evaluate_arity thread mode e
    | Assignment (a, b) -> evaluate_assignment thread mode location a b
    | BoundIdentifier (name, slot)
    | BoundLet (Identifier name, slot) -> Assignable (get_assignable thread.top_frame slot, name)
    | In (a, b) -> evaluate_in thread mode location a b
    | Lambda (return_type, params, modifiers, body) -> evaluate_lambda thread mode return_type (List.to_seq params) modifiers body
    | Call (callee, args, pure) -> evaluate_call thread mode location callee (List.to_seq args) pure
    | _ -> print_endline (show_expression (location, expression)); assert false
  with
    Error message -> raise (Located_error (location, message))

and make_variable_modifiers (modifiers : declaration_modifiers) : variable_modifiers =
  match modifiers with
  | { mut = is_mut } -> { mut = is_mut }

and evaluate_declaration (thread : thread) _ (declaration : declaration) (slot : slot) : unit =
  let assignable = get_assignable thread.top_frame slot in
  set_assignable_modifiers assignable (make_variable_modifiers declaration.modifiers);
  try
    match declaration with
    | { type_expr=Some type_expr; init_expr=Some init_expr; _} ->
      let typ = value_to_type (evaluate_unassignable thread EvalFull type_expr) in
      set_assignable_value assignable (Uninitialized (Some typ));
      let value = evaluate_unassignable thread EvalFull init_expr in
      set_assignable_value assignable (convert_implicit value typ)

    | { type_expr=Some type_expr; init_expr=None; _} ->
      let typ = value_to_type (evaluate_unassignable thread EvalFull type_expr) in
      set_assignable_value assignable (default_value typ);

    | { type_expr=None; init_expr=Some init_expr; _} ->
      let value = evaluate_unassignable thread EvalFull init_expr in
      set_assignable_value assignable value

    | _ -> assert false
  with
    | e -> begin
      set_assignable_value assignable Failed;
      raise e;
    end

and evaluate_order_dependent (thread : thread) (statements : statement Seq.t) : unit =
  Seq.iter (evaluate_statement thread) statements

and evaluate_order_independent (thread : thread) (statements : statement Seq.t) : unit =
  Seq.iter (fun statement -> fork (fun () ->
    evaluate_statement thread statement)) statements

and evaluate_statement (thread : thread) ((location, statement) : statement) : unit = 
  try
    match statement with
    | Expression expression -> ignore (evaluate thread EvalFull expression)
    | BoundDeclaration (declaration, slot) -> evaluate_declaration thread location declaration slot
    | OrderIndependent statements -> evaluate_order_independent thread (List.to_seq statements)
    | Return None -> raise (Return_exn (convert_implicit void thread.top_frame.return_type))
    | Return (Some expression) -> raise (Return_exn (convert_implicit (evaluate_unassignable thread EvalFull expression) thread.top_frame.return_type))
    | _ -> print_endline @@ show_statement (location, statement); assert false
  with
    Error message -> raise (Located_error (location, message))

let evaluate_to_completion (main : unit -> unit) : unit =
  let tasks = Queue.create () in
  Queue.add (main, None) tasks;

  let stalled = Queue.create () in
  while not (Queue.is_empty tasks) do
    let task, dependency = Queue.take tasks in
    if dependency <> None && (let _, slot = Option.get dependency in not (is_value_complete (get_assignable_value slot))) then
      Queue.add (task, dependency) stalled
    else
      match task () with
      | ()
      | exception Saw_failed_error ->
        Queue.transfer stalled tasks
      | exception Located_error (location, message) ->
        print_endline (Printf.sprintf "Error: %s %s" (show_location location) message);
        Queue.transfer stalled tasks
      | exception e ->
        Queue.transfer stalled tasks;
        print_endline (Printexc.to_string e)
      | effect Fork f, k ->
        Queue.add (continue k, None) tasks;
        Queue.add (f, None) tasks;
      | effect Defer dependency, k ->
        Queue.add (continue k, Some dependency) tasks;
  done;

  if not (Queue.is_empty stalled) then
    let dep_name dep = match dep with
      | (_, Some (name, _)) -> name
      | _ -> "" in
    let dependencies = Queue.to_seq stalled |> Seq.map dep_name |> List.of_seq |> List.sort_uniq String.compare in
    print_endline ("Cyclic dependencies detected: " ^ (String.concat ", " dependencies))

let evaluate_program (machine : machine) (statement : statement) : unit =
  let thread = make_thread machine in
  evaluate_to_completion (fun () -> evaluate_statement thread statement)