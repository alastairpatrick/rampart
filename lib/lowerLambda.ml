open Ast
open MapAst

type variable = unit (* TODO *)

type frame = {
  depth: int;
  enclosing_frame: frame option;
  variables: variable array;
  pure: bool;
  const: bool;
}

let make_global_frame (num_globals : int) : frame = {
  depth = 0;
  enclosing_frame = None;
  variables = Array.make num_globals ();
  pure = false;
  const = false;
}

type accumulator = {
  top_frame: frame;
}

let rec visit_expression (frame : frame) ((location, expr): expression) : expression =
  match expr with
  | Lambda (return_type, params, modifiers, ((_, Bound_frame (num_variables, _)) as stmt)) ->
    let num_params = List.length params in
    let lambda_frame = {
      depth = frame.depth + 1;
      enclosing_frame = Some frame;
      variables = Array.make num_variables ();
      pure = modifiers.pure;
      const = modifiers.const;
    } in
    let closure_index = num_params in
    let params = params @ [
      (location, Bound_declaration ({typ=(Pointer Opaque); init_expr=None; name="$closure"; modifiers=empty_declaration_modifiers}, {index=closure_index; depth=lambda_frame.depth; mut=false}))
    ] in
    location, Lambda (return_type, params, modifiers, visit_statement lambda_frame stmt)
  | _ -> location, expr

and visit_statement (frame : frame) (stmt: statement) : statement =
  traverse_statement (visit_statement frame) (visit_expression frame) stmt

let lower_lambda_pass (statement : statement) (num_globals : int): statement =
  let top_frame = make_global_frame num_globals in
  traverse_statement (visit_statement top_frame) (visit_expression top_frame) statement