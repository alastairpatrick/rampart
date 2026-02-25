open Ast
open Effect
open Effect.Deep
open Error
open Location
open Slot
open Type
open Value

type _ Effect.t +=
| Fork : (unit -> unit) -> unit t
| Defer : (string * assignable) -> unit t

type implementation_value +=
  | ImplLambda of statement
  | ImplRepresentative

type machine = {
  globals: value array;
}

type frame = {
  depth: int;
  enclosing_frame: frame option;
  variables: value array;
}

type thread = {
  top_frame: frame;
}

type result_mode =
  | EvalFull        (* Evaluate result of expression fully with all side effects. Both result value and type must be correct. *)
  | EvalTypeOnly    (* Only the type of the result need be correct. Use this to determine type of expression without causing side effects. *)

let fork f = perform (Fork f)
let defer pattern assignable = perform (Defer (pattern, assignable))

let make_thread (machine : machine) : thread = {
  top_frame = {
    depth = 0;
    enclosing_frame = None;
    variables = machine.globals
  };
}

let make_machine (num_globals : int) : machine = {
  globals = Array.make num_globals (Uninitialized None);
}


let convert_implicit (value : value) (to_typ : typ) : value =
  let from_typ = type_of_value value in
  if to_typ = from_typ then
    value
  else begin
    raise error_type_mismatch
    end

let rec representative_value_for_type (typ : typ) : value =
  match typ with
  | Uninitialized -> assert false
  | Singleton Int
  | Singleton Bool
  | Tuple [] ->
    default_value typ
  | Singleton Type ->
    SingletonType Type
  | Singleton singleton_type ->
    Impl (Singleton singleton_type, ImplRepresentative)
  | Tuple types ->
    Tuple (Array.of_list (List.map representative_value_for_type types))

let rec get_assignable frame {index; depth} : assignable =
  if depth = frame.depth then
    index, frame.variables
  else
    get_assignable (Option.get frame.enclosing_frame) {index; depth}

and set_assignable_value (index, value_array) value : unit =
  match value with
  | Uninitialized None | Assignable _ -> assert false
  | _ -> value_array.(index) <- value

and get_assignable_value (index, value_array) : value =
  match value_array.(index) with
  | Failed -> raise Saw_failed_error
  | value -> value

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
  | _ -> print_endline @@ Printf.sprintf "%s %s" (show_value a) (show_value b); assert false

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
      (try
        tuple_value (Array.map2 assign (Array.of_list exprs) values)
      with Invalid_argument _ -> raise (error_type_mismatch))
    | (_, Tuple _), _ -> raise (error_type_mismatch)
    | (location, _), _ -> raise (error_not_assignable location)) in
  assign a b

and evaluate_in thread mode _ a b : value =
  ignore (evaluate_unassignable thread mode a);
  evaluate_unassignable thread mode b

and evaluate_lambda thread mode return_type params body : value =
  let return_type = evaluate_unassignable thread mode return_type |> value_to_type in
  let param_types = List.map (fun (_loc, stmt) ->
    match stmt with
    | BoundDeclaration ({ type_expr=Some type_expr; _ }, _) ->
      evaluate_unassignable thread mode type_expr |> value_to_type
    | _ -> print_endline (show_statement (_loc, stmt)); assert false) params in
  Impl ( Singleton (Function (return_type, param_types)),
    ImplLambda body)
      
and evaluate (thread : thread) (mode : result_mode) ((location, expression) : expression) : value =
  try
    match expression with
    | IntLiteral l -> Int l
    | BoolLiteral b -> Bool b
    | Type Int -> SingletonType Int
    | Type Bool -> SingletonType Bool
    | Type Void -> void
    | Type Type -> SingletonType Type
    | BinaryOp (op, a, b) -> evaluate_binary_op thread mode location op a b
    | Tuple exprs ->
      let values = Array.of_list (List.map (evaluate thread mode) exprs) in
      tuple_value values
    | TypeOf e -> evaluate_typeof thread mode e
    | Arity e -> evaluate_arity thread mode e
    | Assignment (a, b) -> evaluate_assignment thread mode location a b
    | BoundIdentifier (name, slot)
    | BoundLet (Identifier name, slot) -> Assignable (get_assignable thread.top_frame slot, name)
    | In (a, b) -> evaluate_in thread mode location a b
    | Lambda (return_type, params, body) -> evaluate_lambda thread mode return_type params body
    | _ -> print_endline (show_expression (location, expression)); assert false
  with
    Error message -> raise (Located_error (location, message))

let evaluate_declaration thread _ declaration slot =
  let assignable = get_assignable thread.top_frame slot in
  try
    match declaration with
    | { type_expr=Some type_expr; init_expr=Some init_expr; _} ->
      let typ = value_to_type (evaluate thread EvalFull type_expr) in
      set_assignable_value assignable (Uninitialized (Some typ));
      let value = evaluate_unassignable thread EvalFull init_expr in
      set_assignable_value assignable (convert_implicit value typ)

    | { type_expr=Some type_expr; init_expr=None; _} ->
      let typ = value_to_type (evaluate thread EvalFull type_expr) in
      set_assignable_value assignable (default_value typ)

    | { type_expr=None; init_expr=Some init_expr; _} ->
      let value = evaluate_unassignable thread EvalFull init_expr in
      set_assignable_value assignable value

    | _ -> assert false
  with
    | e -> begin
      set_assignable_value assignable Failed;
      raise e;
    end

let rec evaluate_order_independent (thread : thread) (statements : statement list) : unit =
  List.iter (fun statement -> fork (fun () ->
    evaluate_statement thread statement)) statements

and evaluate_statement (thread : thread) ((location, statement) : statement) : unit = 
  try
    match statement with
    | Expression expression -> ignore (evaluate thread EvalFull expression)
    | BoundDeclaration (declaration, slot) -> evaluate_declaration thread location declaration slot
    | OrderIndependent statements -> evaluate_order_independent thread statements
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
  evaluate_to_completion (fun () -> evaluate_statement (make_thread machine) statement)