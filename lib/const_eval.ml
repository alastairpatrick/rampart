(* Big-step interpreter to resolve compile-time constant expressions (CTCE) *)

open Ast
open Bind
open Slot

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
  pure: bool;
}

type eval_mode =
  | Abandon_on_side_effect
  | Substitute_consts_only

let make_global_frame (num_globals : int) : frame = {
  depth = 0;
  enclosing_frame = None;
  variables = Array.make num_globals empty_variable;
  pure = false;
}

let rec get_assignable (frame : frame) ({index; depth}: slot) (display_name : string) : assignable =
  if depth = frame.depth then
    index, frame.variables
  else begin
    get_assignable (Option.get frame.enclosing_frame) {index; depth} display_name
  end

let get_assignable_value (index, variables) : value = 
  variables.(index).value

let set_assignable_value (index, variables) (value : value) : unit =
  variables.(index) <- { value }

let is_const_expression (expression : expression) : bool =
  match expression with
  | _, IntLiteral _ -> true
  | _, Type _ -> true (* NB: if type expressions can incorporate ints, eg if we ever support fixed size arrays, would need to check that the ints are constants *)
  | _ -> false

let rec evaluate_statements env frame mode (statements : statement list) : statement list =
  List.map (evaluate_statement env frame mode) statements

and evaluate_statement (env : env) (frame : frame) (mode : eval_mode) ((location, statement): statement) : statement =
  match statement with
  | Expression expression -> (location, Expression (evaluate_expression env frame mode expression))
  | OrderIndependent statements -> (location, OrderIndependent (evaluate_statements env frame mode statements))
  | BoundDeclaration (declaration, slot) -> (location, evaluate_declaration env frame mode location declaration slot)
  | _ -> print_endline (Printf.sprintf "statement not implemented: %s" (Ast.show_statement (location, statement))); assert false

and evaluate_expression env frame mode ((location, expression): expression) : expression =
  match expression with
  | IntLiteral _
  | Type _ -> (location, expression)
  | BoundIdentifier (display_name, slot) -> evaluate_identifier env frame mode location display_name slot
  | BinaryOp (op, a, b) -> evaluate_binary_op env frame mode location op a b
  | Lambda (return_type, params, modifiers, (body_location, BoundFrame (num_variables, statements))) ->
    let return_type = evaluate_expression env frame mode return_type in
    let lambda_frame = {
      depth = frame.depth + 1;
      enclosing_frame = Some frame;
      variables = Array.make num_variables empty_variable;
      pure = modifiers.pure;
    } in
    let params = List.mapi (fun i (location, param) -> match param with
      | BoundDeclaration (declaration, slot) ->
        let type_expr = evaluate_expression env frame mode (Option.get declaration.type_expr) in
        lambda_frame.variables.(i) <- { value = Non_const_of_type type_expr };
        (location, BoundDeclaration ( { declaration with type_expr = Some type_expr }, slot))
      | _ -> print_endline (Printf.sprintf "parameter not implemented: %s" (Ast.show_statement (location, param))); assert false) params in
    let statements = evaluate_statements env lambda_frame mode statements in
    (location, Lambda (return_type, params, modifiers, (body_location, BoundFrame (num_variables, statements))))
  | _ -> print_endline (Printf.sprintf "expression not implemented: %s" (Ast.show_expression (location, expression))); assert false

and evaluate_identifier _ frame _ location display_name slot =
  let assignable = get_assignable frame slot display_name in
  match get_assignable_value assignable with
  | Uninitialized_of_type _
  | Non_const_of_type _ -> (location, (BoundIdentifier (display_name, slot)))
  | Const_of_value (_, const_expression) -> (location, const_expression)

and evaluate_binary_op env frame mode location op a b =
  let a = evaluate_expression env frame mode a in
  let b = evaluate_expression env frame mode b in
  match op, a, b with
  | Plus, (_, IntLiteral a), (_, IntLiteral b) -> (location, IntLiteral (a + b))
  | Plus, _, _ -> (location, BinaryOp (Plus, a, b))
  | _ -> print_endline (Printf.sprintf "binary operator not implemented: %s %s %s" (Ast.show_expression a) (Ast.show_binary_op op) (Ast.show_expression b)); assert false

  
and type_of_lambda ((location, expression): expression) : expression =
  match expression with
  | Lambda (return_type, params, _, _) ->
    (location, Call (return_type, List.map (fun (_, param) ->
      match param with
      | BoundDeclaration ({type_expr=Some type_expr; _}, _) -> type_expr
      | _ -> assert false) params, false))
  | _ -> assert false

and evaluate_declaration env frame mode _ declaration slot =
  let assignable = get_assignable frame slot declaration.name in
  match declaration with
  | { type_expr=Some type_expr; init_expr=Some init_expr; _} ->
    let type_expr = evaluate_expression env frame mode type_expr in
    let init_expr = implit_convert (evaluate_expression env frame mode init_expr) type_expr in
    if declaration.modifiers.mut || not (is_const_expression init_expr) then
      set_assignable_value assignable (Non_const_of_type type_expr)
    else
      set_assignable_value assignable (Const_of_value init_expr);
    BoundDeclaration ({ declaration with type_expr = Some type_expr; init_expr = Some init_expr }, slot)

  | { type_expr=None; init_expr=Some init_expr; _} ->
    let init_expr = evaluate_expression env frame mode init_expr in
    (* This form of declaration is only used for lambda expressions, which we never treat as constants. *)
    let type_expr = type_of_lambda init_expr in
    set_assignable_value assignable (Non_const_of_type (type_expr));
    BoundDeclaration ({ declaration with type_expr = Some type_expr; init_expr = Some init_expr }, slot)
    
  | _ -> print_endline (Printf.sprintf "declaration not implemented: %s" (Ast.show_declaration declaration)); assert false

and implit_convert (location, value_expression) (_, type_expression) =
  match value_expression, type_expression with
  (* TODO: add some conversions *)
  | _ -> (location, value_expression)
