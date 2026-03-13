(* Big-step interpreter to resolve compile-time constant expressions (CTCE) *)

open Ast
open Bind
open Const
open Error
open Location
open MapAst
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

type external_closure +=
  | Closure of frame * (* ast_alias: *) expression option

type eval_mode =
  | Search_for_declaration_types  (* Transforms from one AST to another, using Evaluate_const to evaluate the constant type of all declaration types, while performing constant folding. *)
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

let rec get_assignable (frame : frame) ({index; depth; mut}: slot) : assignable =
  if depth = frame.depth then
    index, frame.variables
  else begin
    match frame.enclosing_frame with
    | Some enclosing -> get_assignable enclosing {index; depth; mut}
    | None -> raise (error_internal "invalid slot depth")
  end

let get_assignable_value (index, variables) : value = 
  variables.(index).value

let set_assignable_value (index, variables) (value : value) : unit =
  variables.(index) <- { value }

(* Always use this function instead of directly constructing Const_of_value. *)
let check_is_const_value (expression : expression) : value =
  if (is_const_value expression) then begin
    if (const_value_exists (fun e -> match e with (_, Lambda (_, _, _, _, Some (_, Closure (_, None)))) -> true | _ -> false) expression) then
      raise (error_internal "unexpected const value containing a lambda with a closure that has no ast alias");
    Const_of_value expression
  end else
    raise (error_internal (Printf.sprintf "expected const value, got: %s" (Ast.show_expression expression)))


let rec evaluate_statements env frame mode (statements : statement list) : statement list =
  List.map (evaluate_statement env frame mode) statements

and evaluate_order_independent env frame mode statements =
  (* `in_queue` uses a placeholder display name so it has the same pair shape
    as `stalled_queue`.  *)
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
    | Expression expression -> (location, Expression (substitute_lambda_aliases (evaluate_expression env frame mode expression)))
    | Compound statements -> (location, Compound (evaluate_statements env frame mode statements))
    | OrderIndependent statements -> (location, OrderIndependent (evaluate_order_independent env frame mode statements))
    | BoundDeclaration (declaration, slot) -> (location, evaluate_declaration env frame mode location declaration slot)
    | Return e -> (location, Return (substitute_lambda_aliases (evaluate_return env frame mode location e)))
    | _ -> print_endline (Printf.sprintf "statement not implemented: %s" (Ast.show_statement (location, statement))); assert false;
  with Error message -> raise (Located_error (location, message))

and evaluate_expression env frame mode ((location, expression): expression) : expression =
  match expression with
  | IntLiteral _
  | BoolLiteral _
  | Type _ -> (location, expression)
  | BoundIdentifier (display_name, slot) -> evaluate_identifier env frame mode location display_name slot
  | BoundLet _ -> raise (Error "'let' expressions may only appear to the left of an assignment")
  | UnaryOp (op, e) -> evaluate_unary_op env frame mode location op e
  | BinaryOp (op, a, b) -> evaluate_binary_op env frame mode location op a b
  | Conditional (condition, consequent, alternative) -> evaluate_conditional env frame mode location condition consequent alternative
  | Assignment (a, b) -> evaluate_assignment env frame mode location a b
  | In (a, b) -> evaluate_in env frame mode location a b
  | Call (callee, args, modifiers) -> evaluate_call env frame mode location callee args modifiers
  | Tuple elements -> evaluate_tuple env frame mode location elements
  | Arity e -> evaluate_arity env frame mode location e
  | DynamicArray (elements, element_type) -> evaluate_dynamic_array_literal env frame mode location elements element_type
  | Index (array, index) -> evaluate_index env frame mode location array index
  | Lambda (return_type, params, modifiers, (body_location, BoundFrame (num_variables, statement)), closure) ->
    evaluate_lambda env frame mode location return_type params modifiers body_location num_variables statement closure
  | TypeOf e -> evaluate_typeof env frame mode location e
  | _ -> print_endline (Printf.sprintf "expression not implemented: %s" (Ast.show_expression (location, expression))); assert false

and evaluate_expression_opt env frame mode (expr_opt : expression option) : expression option =
  match expr_opt with
  | Some expr -> Some (evaluate_expression env frame mode expr)
  | None -> None

and substitute_lambda_aliases expression : expression =
  let helper = function
  | (_, Lambda (_, _, _, _, Some (_, Closure (_, Some ast_alias)))) -> ast_alias
  | expression -> expression in
  map_expression Fun.id helper expression

(* Expression evaluation guidelines.

Search_for_declaration_types:
DO reduce constant expressions to constant values.
DO reduce sub-expressions even if the whole expression can't be reduced.
DO reduce declaration types to constant values by switching to Evaluate_const mode.
DO NOT type check beyond that absolutely necessary to reduce constant expressions.

Evaluate_type:
DO type check; Evaluate_type mode often erases AST nodes that might contain semantic errors.
DO treat representative values as constant values because they _are_.
DO NOT interpret the value of a representative value as meaningful; only its type is meaningful.
DO NOT return unreduced expressions; the result must be a representative value (and therefore a constant value) or an exception.

Evaluate_const:
DO type check
DO NOT evaluate sub-expressions unless it is semantically correct to do so; such evaluations might have side effects or halt.
DO NOT return unreduced non-constant expressions; the result must be a constant value or an exception.

*)


and evaluate_identifier _ frame mode location display_name ({index; depth; mut} : slot) =
  let assignable = get_assignable frame {index; depth; mut} in
  match mode with
  | Search_for_declaration_types ->
    begin match get_assignable_value assignable with
    | Uninitialized_of_type _ -> raise (Saw_uninitialized display_name)
    | Const_of_value const_value ->
      if mut && (not frame.const || depth <> frame.depth) then
        raise (error_cannot_access_mutable_captured_variable_from_pure_context display_name);
      const_value
    | Non_const_of_type _ -> (location, BoundIdentifier (display_name, {index; depth; mut}))
    end

  | Evaluate_type ->
    begin match get_assignable_value assignable with
    | Uninitialized_of_type None -> raise (Saw_uninitialized display_name)
    | Uninitialized_of_type (Some const_type)
    | Non_const_of_type const_type -> representative_value_of_type const_type
    | Const_of_value const_value -> const_value
    end

  | Evaluate_const ->
    match get_assignable_value assignable with
    | Uninitialized_of_type _ ->
      raise (Saw_uninitialized display_name)
    | Non_const_of_type _ ->
      if not frame.const || depth <> frame.depth then
        raise (error_not_a_compile_time_constant display_name);
      (location, (BoundIdentifier (display_name, {index; depth; mut})))
    | Const_of_value (_, const_expression) ->
      if mut && (not frame.const || depth <> frame.depth) then
        raise (error_cannot_access_mutable_captured_variable_from_pure_context display_name);
      (location, const_expression)

and evaluate_logical_op env frame mode location op a b =
  let a = evaluate_expression env frame mode a in
  match mode with
  | Search_for_declaration_types ->
    let b = evaluate_expression env frame mode b in
    begin match op, a, b with
    | LogicalAnd, (_, BoolLiteral a_value), (_, BoolLiteral b_value) -> (location, BoolLiteral (a_value && b_value))
    | LogicalOr, (_, BoolLiteral a_value), (_, BoolLiteral b_value) -> (location, BoolLiteral (a_value || b_value))
    | _ -> (location, BinaryOp (op, a, b))
    end

  | Evaluate_type -> 
    let b = evaluate_expression env frame mode b in
    begin match a, b with
    | (_, BoolLiteral _), (_, BoolLiteral _) -> representative_value_of_type (location, Type Bool)
    | _ -> raise error_type_mismatch
    end

  | Evaluate_const ->
    begin match op, a with
    | LogicalAnd, (_, BoolLiteral false) -> (location, BoolLiteral false)
    | LogicalAnd, (_, BoolLiteral true) -> evaluate_expression env frame mode b
    | LogicalOr, (_, BoolLiteral false) -> evaluate_expression env frame mode b
    | LogicalOr, (_, BoolLiteral true) -> (location, BoolLiteral true)
    | _, _ -> raise error_type_mismatch
    end

and evaluate_index env frame mode location indexable index =
  let indexable = evaluate_expression env frame mode indexable in

  match index with
  | None when is_const_type indexable -> (location, Index (indexable, None))
  | None -> raise (Error "expected an index sub-expression")
  | Some index ->
    match indexable with
    | _, DynamicArray (elements, Some element_type) ->
      let index = evaluate_expression env frame mode index in
      begin match mode, index with
      | Evaluate_type, (_, IntLiteral _) -> representative_value_of_type element_type (* must not perform a bounds check *)
      | Evaluate_const, (_, IntLiteral i)
      | Search_for_declaration_types, (_, IntLiteral i) ->
        if i < 0 || i >= Array.length elements then
          raise (error_invalid_operation (Printf.sprintf "array index out of bounds: %d" i));
        elements.(i)
      | Search_for_declaration_types, _ -> (location, Index (indexable, Some index))
      | _ -> raise error_type_mismatch
      end

    | _, Tuple elements ->
      let index = evaluate_expression env frame Evaluate_const index in
      begin match index with
      | _, IntLiteral i ->
        (try
          List.nth elements i
        with
        | Invalid_argument _
        | Failure _ -> raise (error_invalid_operation (Printf.sprintf "tuple index out of bounds: %d" i)))
      | _ -> raise error_type_mismatch
      end

    | _ ->
      let indexable_type = evaluate_expression env frame Evaluate_type indexable in
      begin match indexable_type with
      | _, Tuple _ -> location, Index (indexable, Some (evaluate_expression env frame Evaluate_const index))
      | _, DynamicArray _ -> (location, Index (indexable, Some (evaluate_expression env frame mode index)))
      | _ -> raise error_type_mismatch
      end

and evaluate_unary_op env frame mode location op e =
  let e = evaluate_expression env frame mode e in
  match op, e with
  | Negate, (_, IntLiteral v) -> (location, IntLiteral (-v))
  | LogicalNot, (_, BoolLiteral b) -> (location, BoolLiteral (not b))
  | BitwiseInvert, (_, IntLiteral v) -> (location, IntLiteral (lnot v))
  | BitwiseInvert, (_, BoolLiteral b) -> (location, BoolLiteral (not b))
  | _, _ ->
      match mode with
      | Search_for_declaration_types -> (location, UnaryOp (op, e))
      | _ -> raise error_type_mismatch

and evaluate_binary_op env frame mode location op a b =
  if op = LogicalAnd || op = LogicalOr then evaluate_logical_op env frame mode location op a b else
  let a = evaluate_expression env frame mode a in
  let b = evaluate_expression env frame mode b in
  match op, a, b with
  | Plus, (_, IntLiteral a), (_, IntLiteral b) -> (location, IntLiteral (a + b))
  | Minus, (_, IntLiteral a), (_, IntLiteral b) -> (location, IntLiteral (a - b))
  | Times, (_, IntLiteral a), (_, IntLiteral b) -> (location, IntLiteral (a * b))

  | Less, (_, IntLiteral a), (_, IntLiteral b) -> (location, BoolLiteral (a < b))
  | LessEquals, (_, IntLiteral a), (_, IntLiteral b) -> (location, BoolLiteral (a <= b))
  | Greater, (_, IntLiteral a), (_, IntLiteral b) -> (location, BoolLiteral (a > b))
  | GreaterEquals, (_, IntLiteral a), (_, IntLiteral b) -> (location, BoolLiteral (a >= b))

  | Div, (_, IntLiteral num), (_, IntLiteral denom)
  | Modulo, (_, IntLiteral num), (_, IntLiteral denom) ->
    if denom = 0 then begin
      match mode with
      | Search_for_declaration_types -> (location, BinaryOp (op, a, b)) (* TODO: new rule for CTCEs - division and modulo expressions are not CTCEs if the denominator is zero *)
      | Evaluate_type -> representative_value_of_type (location, Type Int)
      | Evaluate_const -> raise (error_invalid_operation "division by zero")
    end else
      (location, IntLiteral (if op = Div then num / denom else num mod denom))

  | ShiftLeft, (_, IntLiteral a), (_, IntLiteral b) -> (location, IntLiteral (a lsl b))
  | ShiftRight, (_, IntLiteral a), (_, IntLiteral b) -> (location, IntLiteral (a asr b))

  | BitwiseAnd, (_, IntLiteral a), (_, IntLiteral b) -> (location, IntLiteral (a land b))
  | BitwiseAnd, (_, BoolLiteral a), (_, BoolLiteral b) -> (location, BoolLiteral (a && b))
  | BitwiseOr, (_, IntLiteral a), (_, IntLiteral b) -> (location, IntLiteral (a lor b))
  | BitwiseOr, (_, BoolLiteral a), (_, BoolLiteral b) -> (location, BoolLiteral (a || b))
  | BitwiseXor, (_, IntLiteral a), (_, IntLiteral b) -> (location, IntLiteral (a lxor b))
  | BitwiseXor, (_, BoolLiteral a), (_, BoolLiteral b) -> (location, BoolLiteral (a <> b))

  | Equals, a, b
  | NotEquals, a, b ->
    if is_const_value a && is_const_value b && (const_types_equal (type_of_expression a) (type_of_expression b)) then
      let are_equal = const_values_equal a b in
      (location, BoolLiteral (if op = Equals then are_equal else not are_equal))
    else begin
      match mode with
      | Search_for_declaration_types -> (location, BinaryOp (op, a, b))
      | _ -> raise error_type_mismatch
    end

  | Plus, _, _
  | Minus, _, _
  | Times, _, _
  | Div, _, _
  | Modulo, _, _
  | Less, _, _
  | LessEquals, _, _
  | Greater, _, _
  | GreaterEquals, _, _ ->
    begin match mode with
    | Search_for_declaration_types -> (location, BinaryOp (op, a, b))
    | _ -> raise error_type_mismatch
    end

  (* TODO: the rest of them *)
  | _ -> print_endline (Printf.sprintf "binary operator not implemented: %s" (Ast.show_binary_op op)); assert false

and evaluate_conditional env frame mode location condition consequent alternative =
  let condition = evaluate_expression env frame mode condition in
  match mode with
  | Search_for_declaration_types ->
    let consequent = evaluate_expression env frame mode consequent in
    let alternative = evaluate_expression env frame mode alternative in
    begin match condition with
    | _, BoolLiteral true -> consequent
    | _, BoolLiteral false -> alternative
    | _ -> (location, Conditional (condition, consequent, alternative))
    end

  | Evaluate_type ->
    let consequent = evaluate_expression env frame mode consequent in
    let alternative = evaluate_expression env frame mode alternative in
    if not (const_types_equal (type_of_expression consequent) (type_of_expression alternative)) then
      raise error_type_mismatch;
    begin match condition with
    | _, BoolLiteral false -> alternative
    | _ -> raise error_type_mismatch
    end
    
  | Evaluate_const ->
    match condition with
    | _, BoolLiteral true -> evaluate_expression env frame mode consequent
    | _, BoolLiteral false -> evaluate_expression env frame mode alternative
    | _ -> raise error_type_mismatch

and evaluate_assignment env frame mode location a b =
  let b = evaluate_expression env frame mode b in
  match mode with
  | Search_for_declaration_types ->
    let rec initialize_bound_lets (a : expression) (b : expression) : unit =
      match a, b with
      | (_, (BoundLet (pattern, slot))), _ ->
        let assignable = get_assignable frame slot in
        if is_const_value b then begin
          let b = match pattern with
          | Identifier name -> set_lambda_aliases b (location, BoundIdentifier (name, slot))
          | _ -> set_lambda_aliases b (location, BoundIdentifier ("_", slot)) in
          set_assignable_value assignable (check_is_const_value b)
        end else
          set_assignable_value assignable (Non_const_of_type (type_of_expression (evaluate_expression env frame Evaluate_type b)))
    
      | (_, Tuple froms), (_, Tuple tos) ->
        (try
          List.iter2 initialize_bound_lets froms tos
        with Invalid_argument _ -> raise error_type_mismatch)

      | (_, Tuple _), _ -> raise error_type_mismatch

      | _ -> ()
    in
    initialize_bound_lets a b;
    (location, Assignment (a, b))

  | Evaluate_type
  | Evaluate_const ->
    let rec assign (a : expression) (b : expression) : expression =
      match a, b with
      | (_, BoundIdentifier (display_name, slot)), _ ->
        let assignable = get_assignable frame slot in
        let value = get_assignable_value assignable in
        begin match mode, value with
        | Evaluate_type, Uninitialized_of_type None -> raise (Saw_uninitialized display_name)
        | Evaluate_type, Uninitialized_of_type (Some const_type)
        | Evaluate_type, Non_const_of_type const_type -> representative_value_of_type const_type
        | Evaluate_type, Const_of_value const_value -> const_value

        | Evaluate_const, Uninitialized_of_type _ -> raise (Saw_uninitialized display_name) (* Raising this leaves the local frame unreachable so any side effects so far don't matter *)
        | Evaluate_const, Non_const_of_type _ -> raise (error_cannot_access_mutable_captured_variable_from_pure_context display_name)
        | Evaluate_const, Const_of_value current ->
          if not slot.mut then
            raise (error_immutable_assignment display_name);
          let b = implicit_convert mode b (type_of_expression current) in
          set_assignable_value assignable (check_is_const_value b);
          b (* The result should be the RHS, implicitly converted to the same type as the LHS *)

        | Search_for_declaration_types, _ -> assert false
        end

      | (_, BoundLet (_, slot)), _ ->
        let assignable = get_assignable frame slot in
        (* This goes quite a bit differently than for BoundIdentifier. The main reason is because the assignment of a BoundLet _is_ it's initialization,
           whereas, BoundIdentifiers are always initialized before any reassignment. *)
        set_assignable_value assignable (check_is_const_value b);
        b (* The result should be the RHS, implicitly converted to the same type as the LHS, but the type of the LHS is inferred from the RHS in this case *)

      | (_, Tuple froms), (_, Tuple tos) ->
        (try
          (location, Tuple (List.map2 assign froms tos))
        with Invalid_argument _ -> raise error_type_mismatch)

      | (_, Tuple _), _ -> raise error_type_mismatch

      | _ -> raise (error_internal (Printf.sprintf "assignment target not implemented: %s" (Ast.show_expression a))) in
    assign a b

and evaluate_in env frame mode location a b =
  let a = evaluate_expression env frame mode a in
  let b = evaluate_expression env frame mode b in
  match mode with
  | Search_for_declaration_types -> (location, In (a, b))
  | Evaluate_type
  | Evaluate_const -> b

and evaluate_call env frame mode location callee args type_modifiers =
  (* Consistent with other imperative languages, semantically, the callee is evaluated before any arguments. *)
  let callee = evaluate_expression env frame mode callee in
  let args = List.map (evaluate_expression env frame mode) args in
  let type_modifiers = { type_modifiers with pure = type_modifiers.pure || type_modifiers.const } in
  match callee with
  | _, Lambda (return_type, params, lambda_modifiers, (_, BoundFrame (num_variables, statement)), Some (_, Closure (closure_frame, _))) ->
    begin match mode with
    | Search_for_declaration_types ->
      if lambda_modifiers.const && is_const_value callee && List.for_all is_const_value args then
        evaluate_expression env frame Evaluate_const (location, Call (callee, args, type_modifiers))
      else
        (location, Call (callee, args, type_modifiers))

    | Evaluate_type ->
      representative_value_of_type return_type

    | Evaluate_const ->
      if not lambda_modifiers.const then
        raise (error_invalid_operation "cannot call non-const lambda in a constant expression");
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
          set_assignable_value (get_assignable callee_frame slot) (check_is_const_value arg)
        | _ -> raise (error_internal (Printf.sprintf "parameter not implemented: %s" (Ast.show_statement (location, param))))) params;
      try
        evaluate_statement env callee_frame mode statement |> ignore;
        match return_type with
        | _, Tuple [] -> (location, Tuple [])
        | _ -> raise (Error "missing return statement")
      with
      | Return_exn return_value ->
        if not (is_const_value return_value) then
          raise (error_internal "non-constant return value should be impossible");
        return_value

    end

  | _, Lambda _ -> raise (error_internal "all lambda should have closures added before calling them" )

  | _ -> (location, Call (callee, args, type_modifiers))

and evaluate_tuple env frame mode location elements =
  (location, Tuple (List.map (evaluate_expression env frame mode) elements))
  
and evaluate_dynamic_array_literal env frame mode location elements element_type : expression =
  if Array.length elements = 0 then begin
    match element_type with
    | Some _ -> (location, DynamicArray (elements, element_type))
    | _ ->
      (* TODO: we plan to allow empty array literals in some special cases where the element type is known, including initializers, the RHS of some assignments and function call arguments *)
      raise (Error "cannot infer type of empty array literal")
  end else begin
    let elements = Array.map (evaluate_expression env frame mode) elements in

    (* Search_for_declaration_types is responsible for checking all the elements are the same type iff
      it is necessary to do so the for constant folding, i.e. if the resulting array literal will be
      considered a constant value. *)
    if mode <> Search_for_declaration_types || Array.for_all is_const_value elements then begin
      let element_type = match element_type with
      | Some element_type -> element_type
      | _ -> type_of_expression elements.(0) in
      if Array.exists (fun e -> not (const_types_equal (type_of_expression e) element_type)) elements then
        raise error_type_mismatch;
      (location, DynamicArray (elements, Some element_type))
    end else
      (location, DynamicArray (elements, element_type))
  end

and evaluate_arity env frame mode location e =
  match mode with
  | Search_for_declaration_types ->
    let e = evaluate_expression env frame mode e in
    begin match evaluate_expression env frame mode e with
    | _, Tuple elements -> (location, IntLiteral (List.length elements))
    | _ when is_const_value e -> (location, IntLiteral 1)
    | _ -> (location, Arity e)
    end

  | Evaluate_type -> representative_value_of_type (location, Type Int)
  | Evaluate_const ->
    let e = evaluate_expression env frame mode e in
    match e with
    | _, Tuple elements -> (location, IntLiteral (List.length elements))
    | _ -> (location, IntLiteral 1)

and evaluate_lambda_part1 _ frame mode location return_type params modifiers body_location num_variables statement =
  match mode with
  | Evaluate_type ->
    representative_value_of_type (type_of_expression (location, Lambda (return_type, params, modifiers, (body_location, BoundFrame (num_variables, statement)), None)))
  | _ ->
    let modifiers = { modifiers with pure = modifiers.pure || modifiers.const } in
    if frame.const && not modifiers.const then
      raise error_expected_const_lambda;
    (location, Lambda (return_type, params, modifiers, (body_location, BoundFrame (num_variables, statement)), Some (distinct_closure_identity (), Closure (frame, None))))

and evaluate_lambda_part2 env mode part1 =
  match mode, part1 with
  | Evaluate_type, _ ->
    part1
  | _, (location, Lambda (return_type, params, modifiers, (body_location, BoundFrame (num_variables, statement)), Some (closure_identity, Closure (frame, _)))) ->
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
    let statement = evaluate_statement env lambda_frame Search_for_declaration_types statement in
    (* A subsequent pass will verify that the lambda meets the requirements for pure or const. *)
    (location, Lambda (return_type, params, modifiers, (body_location, BoundFrame (num_variables, statement)), Some (closure_identity, Closure (frame, None))))
  | _ -> assert false

and evaluate_lambda env frame mode location return_type params modifiers body_location num_variables statement _ =
  let part1 = evaluate_lambda_part1 env frame mode location return_type params modifiers body_location num_variables statement in
  evaluate_lambda_part2 env mode part1

and evaluate_typeof env frame _ _ e =
  type_of_expression (evaluate_expression env frame Evaluate_type e)

and set_lambda_aliases (location, const_value) ast_alias =
  let ith_index i e = set_lambda_aliases e (location, Index (ast_alias, Some (location, (IntLiteral i)))) in
  match const_value with
  | Lambda (return_type, params, modifiers, statement, Some (closure_identity, Closure (frame, _))) ->
    (location, Lambda (return_type, params, modifiers, statement, Some (closure_identity, Closure (frame, Some ast_alias))))
  | Tuple elements -> (location, Tuple (List.mapi ith_index elements))
  | DynamicArray (elements, element_type) -> (location, DynamicArray ((Array.mapi ith_index elements), element_type))
  | _ -> (location, const_value)

and evaluate_declaration env frame mode location declaration slot =
  assert (mode <> Evaluate_type);

  let assignable = get_assignable frame slot in

  let initialize_assignable type_expr init_expr =
    if (declaration.modifiers.mut || not (is_const_value init_expr)) then begin
      if mode=Evaluate_const && frame.const then
        let init_expr = set_lambda_aliases init_expr (location, BoundIdentifier (declaration.name, slot)) in
        set_assignable_value assignable (check_is_const_value init_expr)
      else        
        set_assignable_value assignable (Non_const_of_type type_expr)
    end else
      let init_expr = set_lambda_aliases init_expr (location, BoundIdentifier (declaration.name, slot)) in
      set_assignable_value assignable (check_is_const_value init_expr) in
      
  match declaration with
  | { type_expr=Some type_expr; init_expr=Some init_expr; _} ->
    let type_expr = check_is_const_type (evaluate_expression env frame Evaluate_const type_expr) in
    set_assignable_value assignable (Uninitialized_of_type (Some type_expr));
    let init_expr = implicit_convert mode (evaluate_expression env frame mode init_expr) type_expr in
    initialize_assignable type_expr init_expr;
    BoundDeclaration ({ declaration with type_expr = Some type_expr; init_expr = Some (substitute_lambda_aliases init_expr) }, slot)

  | { type_expr=Some type_expr; init_expr=None; _} ->
    let type_expr = check_is_const_type (evaluate_expression env frame Evaluate_const type_expr) in
    let init_expr = default_value type_expr in
    initialize_assignable type_expr init_expr;
    BoundDeclaration ({ declaration with type_expr = Some type_expr; init_expr = Some (substitute_lambda_aliases init_expr) }, slot)

  (* This form of declaration is only used for lambda expressions. *)
  | { type_expr=None; init_expr=Some (location, Lambda (return_type, params, modifiers, (body_location, BoundFrame (num_variables, statement)), _)) ; _} ->
    let init_expr = match get_assignable_value assignable with
    | Const_of_value part1 -> part1 (* If a previous attempt at part 2 aborted, skip part 1, ensuring that closure identity is preserved. *)
    | _ ->
      evaluate_lambda_part1 env frame mode location return_type params modifiers body_location num_variables statement in
    (initialize_assignable (type_of_expression init_expr) init_expr;
    let init_expr = evaluate_lambda_part2 env mode init_expr in
    let type_expr = check_is_const_type (type_of_expression init_expr) in
    initialize_assignable type_expr init_expr;
    BoundDeclaration ({ declaration with type_expr = Some type_expr; init_expr = Some (substitute_lambda_aliases init_expr) }, slot))
    
  | _ -> print_endline (Printf.sprintf "declaration not implemented: %s" (Ast.show_declaration declaration)); assert false

and evaluate_return env frame mode _ e =
  let e = implicit_convert mode (evaluate_expression env frame mode e) frame.return_type in
  match mode with
    | Search_for_declaration_types -> e
    | Evaluate_type -> assert false
    | Evaluate_const -> raise (Return_exn e)


and implicit_convert mode from_expression to_type =
  match mode with
  | Search_for_declaration_types -> from_expression (* just leave the node in place for a subsequent pass to actually do the implicit conversion *)
  | Evaluate_type -> assert false; (* never actually called in this mode *)
    (*representative_value_of_type (to_type_location, to_type)*) (* leave it to a subsequent pass to determine whether the conversion is valid *)
  | Evaluate_const ->
    let from_type = type_of_expression from_expression in
    match to_type with
    | _, Type Type when is_const_type from_expression -> from_expression
    | _ when const_types_equal from_type to_type -> from_expression
    | _ -> raise error_type_mismatch

let const_evaluate_program (env : env) (frame : frame) (statement : statement) : statement =
  evaluate_statement env frame Search_for_declaration_types statement
