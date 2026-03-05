(* Big-step interpreter to resolve compile-time constant expressions (CTCE) *)

open Ast
open Bind
open Error
open Location
open Slot

(* Where possible, prefer to recover from errors in this pass, relying on a later pass to report them. Exceptions:
  - It's okay to raise exceptions that will be caught within this module, such as Saw_uninitialized.
  - Raise internal errors any time something "impossible" happens, for example if we encounter an AST node that we forgot to implement a case for. This is primarily to make it easier to detect and fix bugs in this module. Prefer these to assertions.
  - Located_errors wrapping exceptions that this module must raise anyway is fine.
  - Raise an Error exception when recovery is not practical.
*)

exception Saw_uninitialized of string
exception Return_exn of expression

type value =
| Uninitialized_of_type of (* expression_type: *) expression option
| Const_of_value of expression
| Non_const_of_type of expression
| Non_const_of_value of expression

type variable = {
  value: value;
}

type assignable = (* array_idx: *) int * variable array

let empty_variable = { value = Uninitialized_of_type None }

type frame = {
  depth: int;
  enclosing_frame: frame option;
  variables: variable array;
  return_type: expression;
  pure: bool;
  const: bool;
}

type closure +=
  | Closure of frame

type eval_mode =
  | Search_for_declaration_types  (* Search AST for declarations and switch to Evaluate_const mode to evaluate their types *)
  | Evaluate_type                 (* Evaluate the type of an expression without causing side-effects. Returns a type representative rather than the type itself. Not used on statements. *)
  | Evaluate_const                (* Compile-time evaluation of constant expressions *)

let make_global_frame (num_globals : int) : frame = {
  depth = 0;
  enclosing_frame = None;
  variables = Array.make num_globals empty_variable;
  return_type = (null_location, Type Void);
  pure = false;
  const = false;
}

let rec get_assignable (frame : frame) ({index; depth}: slot) : assignable =
  if depth = frame.depth then
    index, frame.variables
  else begin
    match frame.enclosing_frame with
    | Some enclosing -> get_assignable enclosing {index; depth}
    | None -> raise (error_internal "invalid slot depth")
  end

let get_assignable_value (index, variables) : value = 
  variables.(index).value

let rec has_binds expression =
  match expression with
  | (_, BoundIdentifier _)
  | (_, BoundLet _) -> true
  | (_, Tuple elements) -> List.exists has_binds elements
  | _ -> false

let set_assignable_value (index, variables) (value : value) : unit =
  match value with
  | Const_of_value expression when has_binds expression ->
    raise (error_internal "RHS of assignment should be impossible")
  | _ ->
    variables.(index) <- { value }

(* Constant expression aka compile-time constant expression (CTCE): an expression that can be evaluated to a const value at compile time
   Constant value: a literal, a constant type, a const lambda expression or a tuple of constant values. Subset of the constant expressions.
   Constant type: a constant value corresponding to a type. Subset of the constant values.
   Representative value: a value of a particular type that represents that type. Only the type of a representative value is meaningful.

   Constant expression > constant value > constant type
*)

let rec is_const_type (expression : expression) : bool =
  match expression with
  | _, Type _ -> true
  | _, Tuple elements -> List.for_all is_const_type elements
  | _, Call (callee, param_types, _) ->
    is_const_type callee && List.for_all is_const_type param_types
  | _ -> false

let check_is_const_type expression =
  if is_const_type expression then expression else raise error_type_expected

let rec is_const_value (expression : expression) : bool =
  match expression with
  | _, IntLiteral _ -> true
  | _, Tuple elements -> List.for_all is_const_value elements
  | _, Lambda (_, _, {const = true; _}, _, _) -> true
  | _ when is_const_type expression -> true
  | _ -> false

(* This must work on any const value, any lambda (const or not) and any representative value. *)
let rec type_of_expression ((location, expression): expression) : expression =
  match expression with
  | IntLiteral _ -> (location, Type Int)
  | BoolLiteral _ -> (location, Type Bool)
  | Type _ -> (location, Type Type)
  | Tuple elements -> (location, Tuple (List.map type_of_expression elements))
  | TypeOf _ -> (location, Type Type)
  | Lambda (return_type, params, modifiers, _, _) ->
    let param_types = List.map (fun (_, param) -> match param with
      | BoundDeclaration ({type_expr=Some type_expr; _}, _) -> type_expr
      | _ -> assert false) params in
    (location, Call(return_type, param_types, modifiers))
  | _ when is_const_type (location, expression) -> (location, Type Type)
  | _ -> print_endline (Printf.sprintf "expression not implemented: %s" (Ast.show_expression (location, expression))); assert false (* TODO: implement for more expressions as needed *)

let rec default_value ((location, const_type): expression) : expression =
  match const_type with
  | Type Int -> (location, IntLiteral 0)
  | Type Bool -> (location, BoolLiteral false)
  | Tuple elements ->
    (location, Tuple (List.map default_value elements))
  | _ -> raise error_no_default_value

let rec representative_value_of_type ((location, const_type): expression) : expression =
  match const_type with
  | Type Int -> (location, IntLiteral 0)
  | Type Bool -> (location, BoolLiteral false)
  | Type Type -> (location, Type Type)
  | Tuple elements ->
    (location, Tuple (List.map representative_value_of_type elements))
  | Call (return_type, param_types, modifiers) ->
    (location, Lambda (return_type,
      List.map (fun param_type -> (location, BoundDeclaration ({type_expr=Some param_type; init_expr=None; name=""; modifiers=empty_declaration_modifiers}, {index=0; depth=0}))) param_types,
      modifiers, (location, Compound []), None))
  | _ -> raise (error_internal (Printf.sprintf "representative value not implemented for type expression: %s" (Ast.show_expression (location, const_type)))) 

let rec evaluate_statements env frame mode (statements : statement list) : statement list =
  List.map (evaluate_statement env frame mode) statements

and evaluate_order_independent env frame mode statements =
  (* `in_queue` uses a placeholder display name so it has the same pair shape
    as `stalled_queue`. `stalled_queue` holds entries of the form
    ((location, statement), display_name) so the pass can reliably
    produce diagnostics tied to the original statement location. *)
  let in_queue = Queue.of_seq (Seq.map (fun s -> (s, "")) (List.to_seq statements)) in
  let stalled_queue = Queue.create () in
  let out_queue = Queue.create() in
  let progress_made = ref false in
  while not (Queue.is_empty in_queue) do
    while not (Queue.is_empty in_queue) do
      let (statement, _) = Queue.take in_queue in
      match evaluate_statement env frame mode statement with
      | exception Saw_uninitialized display_name ->
        Queue.add (statement, display_name) stalled_queue;

      | evaluated_statement ->
        progress_made := true;
        Queue.add evaluated_statement out_queue
    done;

    if not !progress_made then begin
      match List.of_seq (Queue.to_seq stalled_queue) with
        | [] -> raise (error_internal "a dependency cycle with no nodes should be impossible");
        | head :: tail ->
          let display_name (_, n) = n in
          let location_of ((l, _), _) = l in
          let msg = Printf.sprintf "found cyclic dependency: %s -> %s"
            (String.concat " -> " (List.map display_name (head::tail)))
            (display_name head)
          in
          raise (Located_error (location_of(head), msg))
    end;

    Queue.transfer stalled_queue in_queue;
    progress_made := false
  done;
  List.of_seq (Queue.to_seq out_queue)

and evaluate_statement (env : env) (frame : frame) (mode : eval_mode) ((location, statement): statement) : statement =
  try
    match statement with
    | Expression expression -> (location, Expression (evaluate_expression env frame mode expression))
    | OrderIndependent statements -> (location, OrderIndependent (evaluate_order_independent env frame mode statements))
    | BoundDeclaration (declaration, slot) -> (location, evaluate_declaration env frame mode location declaration slot)
    | Return e -> (location, Return (evaluate_return env frame mode location e))
    | _ -> print_endline (Printf.sprintf "statement not implemented: %s" (Ast.show_statement (location, statement))); assert false;
  with Error message -> raise (Located_error (location, message))

and evaluate_expression env frame mode ((location, expression): expression) : expression =
  match expression with
  | IntLiteral _
  | BoolLiteral _
  | Type _ -> (location, expression)
  | BoundIdentifier (display_name, slot) -> evaluate_identifier env frame mode location display_name slot
  | BoundLet _ -> raise (Error "'let' expressions may only appear to the left of an assignment")
  | BinaryOp (op, a, b) -> evaluate_binary_op env frame mode location op a b
  | Assignment (a, b) -> evaluate_assignment env frame mode location a b
  | Call (callee, args, modifiers) -> evaluate_call env frame mode location callee args modifiers
  | Tuple elements -> evaluate_tuple env frame mode location elements
  | Arity e -> evaluate_arity env frame mode location e
  | Lambda (return_type, params, modifiers, (body_location, BoundFrame (num_variables, statements)), _) ->
    evaluate_lambda env frame mode location return_type params modifiers body_location num_variables statements
  | TypeOf e -> evaluate_typeof env frame mode location e
  | _ -> print_endline (Printf.sprintf "expression not implemented: %s" (Ast.show_expression (location, expression))); assert false

and evaluate_identifier _ frame mode location display_name ({index; depth} : slot) =
  match mode with
  | Search_for_declaration_types ->
    (location, BoundIdentifier (display_name, {index; depth}))

  | Evaluate_type ->
    let assignable = get_assignable frame {index; depth} in
    begin match get_assignable_value assignable with
    | Uninitialized_of_type None -> raise (Saw_uninitialized display_name)
    | Uninitialized_of_type (Some const_type)
    | Non_const_of_type const_type -> representative_value_of_type const_type
    | Const_of_value const_value
    | Non_const_of_value const_value -> const_value
    end

  | Evaluate_const ->
    let assignable = get_assignable frame {index; depth} in
    match get_assignable_value assignable with
    | Uninitialized_of_type _ ->
      raise (Saw_uninitialized display_name)
    | Non_const_of_type _ ->
      if not frame.const || depth <> frame.depth then
        raise (error_not_a_compile_time_constant display_name);
      (location, (BoundIdentifier (display_name, {index; depth})))
    | Const_of_value (_, const_expression) ->
      (location, const_expression)
    | Non_const_of_value (_, const_expression) ->
      if not frame.const || depth <> frame.depth then begin
        raise (error_cannot_access_mutable_captured_variable_from_pure_context display_name);
      end;
      (location, const_expression)

and evaluate_binary_op env frame mode location op a b =
  let a = evaluate_expression env frame mode a in
  let b = evaluate_expression env frame mode b in
  match op, a, b with
  | Plus, (_, IntLiteral a), (_, IntLiteral b) -> (location, IntLiteral (a + b))
  | Plus, _, _ -> (location, BinaryOp (Plus, a, b))
  | _ -> print_endline (Printf.sprintf "binary operator not implemented: %s %s %s" (Ast.show_expression a) (Ast.show_binary_op op) (Ast.show_expression b)); assert false

and evaluate_assignment env frame mode location a b =
  match mode with
  | Search_for_declaration_types ->
    let b = evaluate_expression env frame mode b in
    (* a is not searched here because there should be no declarations to find on the LHS of an assignment and there should be nothing to normalize on the LHS of an assignment *)
    (location, Assignment (a, b))

  | Evaluate_type ->
    (* The result should be the RHS, implicitly converted to the same type as the LHS. The value doesn't matter in this case, so return any value with the same type as the LHS *)
    evaluate_expression env frame mode a

  | Evaluate_const ->
    let b = evaluate_expression env frame mode b in
    let rec assign (a : expression) (b : expression) : expression =
      match a, b with
      | (_, BoundIdentifier (display_name, slot)), _ ->
        let assignable = get_assignable frame slot in
        let value = get_assignable_value assignable in
        begin match value with
        | Uninitialized_of_type _ -> raise (Saw_uninitialized display_name) (* Raising this leaves the local frame unreachable so any side effects so far don't matter *)
        | Non_const_of_type _ -> raise (error_cannot_access_mutable_captured_variable_from_pure_context display_name)
        | Const_of_value _ -> raise (error_immutable_assignment display_name)
        | Non_const_of_value current ->
          let b = implicit_convert mode b (type_of_expression current) in
          set_assignable_value assignable (Non_const_of_value b);
          b (* The result should be the RHS, implicitly converted to the same type as the LHS *)
        end

      | (_, BoundLet (_, slot)), _ ->
        let assignable = get_assignable frame slot in
        (* This goes quite a bit differently than for BoundIdentifier. The main reason is because the assignment of a BoundLet _is_ it's initialization,
           whereas, BoundIdentifiers are always initialized before any reassignment. *)
        set_assignable_value assignable (Const_of_value b);
        b (* The result should be the RHS, implicitly converted to the same type as the LHS, but the type of the LHS is inferred from the RHS in this case *)

      | (_, Tuple froms), (_, Tuple tos) ->
        (try
          (location, Tuple (List.map2 assign froms tos))
        with Invalid_argument _ -> raise error_type_mismatch)

      | (_, Tuple _), _ -> raise error_type_mismatch

      | _ -> raise (error_internal (Printf.sprintf "assignment target not implemented: %s" (Ast.show_expression a))) in
    assign a b

and evaluate_call env frame mode location callee args modifiers =
  (* Consistent with other imperative languages, semantically, the callee is evaluated before any arguments. *)
  let callee = evaluate_expression env frame mode callee in
  let args = List.map (evaluate_expression env frame mode) args in
  match callee with
  | _, Lambda (return_type, _, _, _, _) when mode = Evaluate_type ->
    representative_value_of_type return_type

  | _, Lambda (return_type, params, lambda_modifiers, (_, BoundFrame (num_variables, statements)), Some Closure closure_frame) ->
    begin match mode with
    | Search_for_declaration_types ->
      (location, Call (callee, args, modifiers))

    | Evaluate_type ->
      representative_value_of_type return_type

    | Evaluate_const ->
      assert lambda_modifiers.const; (* See evaluate_lambda *)
      let callee_frame = {
        depth = closure_frame.depth+1;
        enclosing_frame = Some closure_frame;
        variables = Array.make num_variables empty_variable;
        return_type = return_type;
        pure = true;
        const = true;
      } in
      List.iteri (fun i (location, param) -> match param with
        | BoundDeclaration ({type_expr=Some type_expr; _}, slot) ->
          let arg = List.nth args i in
          let arg = implicit_convert mode arg type_expr in
          set_assignable_value (get_assignable callee_frame slot) (Const_of_value arg)
        | _ -> raise (error_internal (Printf.sprintf "parameter not implemented: %s" (Ast.show_statement (location, param))))) params;
      try
        evaluate_statements env callee_frame mode statements |> ignore;
        (location, Tuple [])
      with
      | Return_exn return_value ->
        if not (is_const_value return_value) then
          raise (error_internal "non-constant return value should be impossible");
        return_value

    end

  | _ -> (location, Call (callee, args, modifiers))

and evaluate_tuple env frame mode location elements =
  (location, Tuple (List.map (evaluate_expression env frame mode) elements))
  
and evaluate_arity env frame mode location e =
  match mode with
  | Search_for_declaration_types ->
    let e = evaluate_expression env frame mode e in
    (location, Arity e)
  | Evaluate_type -> representative_value_of_type (location, Type Int)
  | Evaluate_const ->
    let e = evaluate_expression env frame mode e in
    match e with
    | _, Tuple elements -> (location, IntLiteral (List.length elements))
    | _ -> (location, IntLiteral 1)

and evaluate_lambda env frame mode location return_type params modifiers body_location num_variables statements =
  match mode with
  | Evaluate_type ->
    representative_value_of_type (type_of_expression (location, Lambda (return_type, params, modifiers, (body_location, BoundFrame (num_variables, statements)), None)))
  | _ ->
    let modifiers = { modifiers with pure = modifiers.pure || modifiers.const } in
    if frame.const && not modifiers.const then
      raise error_expected_const_lambda;
    let lambda_frame = {
      depth = frame.depth + 1;
      enclosing_frame = Some frame;
      variables = Array.make num_variables empty_variable;
      return_type = return_type;
      pure = modifiers.pure;
      const = modifiers.const
    } in
    let return_type = check_is_const_type (evaluate_expression env frame Evaluate_const return_type) in
    let params = List.map (fun (location, param) -> match param with
      | BoundDeclaration ({init_expr=init_expr; type_expr=Some type_expr; name=name; modifiers=modifiers}, slot) ->
        let type_expr = check_is_const_type (evaluate_expression env frame Evaluate_const type_expr) in
        set_assignable_value (get_assignable lambda_frame slot) (Non_const_of_type type_expr);
        (location, BoundDeclaration ( { init_expr=init_expr; type_expr = Some type_expr; name=name; modifiers=modifiers }, slot))
      | _ -> raise (error_internal (Printf.sprintf "parameter not implemented: %s" (Ast.show_statement (location, param))))) params in
    let statements = evaluate_statements env lambda_frame Search_for_declaration_types statements in
    (* A subsequent pass will verify that the lambda meets the requirements for pure or const. *)
    (location, Lambda (return_type, params, modifiers, (body_location, BoundFrame (num_variables, statements)), if modifiers.const then Some (Closure frame) else None))

and evaluate_typeof env frame _ _ e =
  type_of_expression (evaluate_expression env frame Evaluate_type e)

and evaluate_declaration env frame mode _ declaration slot =
  assert (mode <> Evaluate_type);

  let assignable = get_assignable frame slot in

  let initialize_assignable type_expr init_expr =
    if (declaration.modifiers.mut || not (is_const_value init_expr)) then begin
      if mode=Evaluate_const && frame.const then
        set_assignable_value assignable (Non_const_of_value init_expr)
      else        
        set_assignable_value assignable (Non_const_of_type type_expr)
    end else
      set_assignable_value assignable (Const_of_value init_expr) in
      
  match declaration with
  | { type_expr=Some type_expr; init_expr=Some init_expr; _} ->
    let type_expr = check_is_const_type (evaluate_expression env frame Evaluate_const type_expr) in
    set_assignable_value assignable (Uninitialized_of_type (Some type_expr));
    let init_expr = implicit_convert mode (evaluate_expression env frame mode init_expr) type_expr in
    initialize_assignable type_expr init_expr;
    BoundDeclaration ({ declaration with type_expr = Some type_expr; init_expr = Some init_expr }, slot)

  | { type_expr=Some type_expr; init_expr=None; _} ->
    let type_expr = check_is_const_type (evaluate_expression env frame Evaluate_const type_expr) in
    let init_expr = default_value type_expr in
    initialize_assignable type_expr init_expr;
    BoundDeclaration ({ declaration with type_expr = Some type_expr; init_expr = Some init_expr }, slot)

  | { type_expr=None; init_expr=Some init_expr; _} ->
    let init_expr = evaluate_expression env frame mode init_expr in
    (* This form of declaration is only used for lambda expressions. *)
    let type_expr = check_is_const_type (type_of_expression init_expr) in
    initialize_assignable type_expr init_expr;
    BoundDeclaration ({ declaration with type_expr = Some type_expr; init_expr = Some init_expr }, slot)
    
  | _ -> print_endline (Printf.sprintf "declaration not implemented: %s" (Ast.show_declaration declaration)); assert false

and evaluate_return env frame mode _ e =
  let e = evaluate_expression env frame mode e in
  match mode with
    | Search_for_declaration_types -> e
    | Evaluate_type -> assert false
    | Evaluate_const -> raise (Return_exn e)


and implicit_convert mode (value_location, value_expression) (_, to_type) =
  match mode with
  | Search_for_declaration_types -> (value_location, value_expression) (* just leave the node in place for a subsequent pass to actually do the implicit conversion *)
  | Evaluate_type -> assert false; (* never actually called in this mode *)
    (*representative_value_of_type (to_type_location, to_type)*) (* leave it to a subsequent pass to determine whether the conversion is valid *)
  | Evaluate_const ->
    let (_, from_type) = type_of_expression (value_location, value_expression) in
    if from_type = to_type then
      (* TODO: add some conversions *)
      (value_location, value_expression)
    else
      raise error_type_mismatch
