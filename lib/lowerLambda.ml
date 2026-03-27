open Ast
open MapAst

(*type variable = unit  *)

type frame = {
  depth: int;
  (*enclosing_frame: frame option;
  variables: variable array;
  pure: bool;
  const: bool;*)
}

let make_global_frame (_ : int) : frame = {
  depth = 0;
  (*enclosing_frame = None;
  variables = Array.make num_globals ();
  pure = false;
  const = false;*)
}

let rec lower_const_type (frame : frame) (typ: const_type_expression) : const_type_expression =
  map_const_type_children (lower_expression frame) (lower_const_type frame) (match typ with
    | Function (return_type, param_types, modifiers) ->
      let param_types = param_types @ [Pointer Opaque] in (* add an extra parameter for the closure *)
      Function (return_type, param_types, modifiers)
    | _ -> typ)

and lower_expression (frame : frame) ((location, expr): expression) : expression =
  let lower_expression_children frame expr = map_expression_children (lower_statement frame) (lower_expression frame) (lower_const_type frame) expr in
  match expr with
  | Lambda (return_type, params, modifiers, ((_, Bound_frame (_, _)) as stmt)) ->
    let closure_index = List.length params in
    let params = (List.map (lower_statement frame) params) in
    let return_type = lower_const_type frame return_type in
    let lambda_frame = {
      depth = frame.depth + 1;
      (*enclosing_frame = Some frame;
      variables = Array.make num_variables ();
      pure = modifiers.pure;
      const = modifiers.const;*)
    } in
    let stmt = lower_statement lambda_frame stmt in
    location, Lambda (return_type, params @ [
      (location, Bound_declaration ({typ=(Pointer Opaque); init_expr=None; name="$closure"; modifiers=empty_declaration_modifiers}, {index=closure_index; depth=lambda_frame.depth; mut=false}))
      ], modifiers, stmt)

  | _ -> lower_expression_children frame (location, expr)

and lower_statement (frame : frame) (stmt: statement) : statement =
  map_statement_children (lower_statement frame) (lower_expression frame) (lower_const_type frame) stmt

let lower_lambda_pass (statement : statement) (num_globals : int): statement =
  let top_frame = make_global_frame num_globals in
  lower_statement top_frame statement