open Ast

(* Map only the child expressions and nested const_type_expressions of a const_type.
   This helper does not transform the top-level const_type node itself; that is
   the responsibility of the caller. This makes it safe to build non-self-looping
   recursion for AST rewrites. *)
let map_const_type_children (ef : expression -> expression) (tf : const_type_expression -> const_type_expression) (typ: const_type_expression) : const_type_expression =
  match typ with
  | Bool
  | Deduced
  | Int
  | Opaque
  | Representative
  | Type -> typ

  | Dynamic_array element_type ->
    Dynamic_array (tf element_type)
  | Function (return_type, param_types, modifiers) ->
    Function (tf return_type, List.map tf param_types, modifiers)
  | Pointer pointee_type ->
    Pointer (tf pointee_type)
  | Tuple element_types ->
    Tuple (List.map tf element_types)
  | Unevaluated type_expr -> Unevaluated (ef type_expr)

let map_statement_children (sf: statement -> statement) (ef : expression -> expression) (tf : const_type_expression -> const_type_expression) ((location, stmt): statement) : statement =
  match stmt with
  | Bound_declaration (({ typ; init_expr; _ } as decl), slot) ->
    location, Bound_declaration ({ decl with typ = map_const_type_children ef tf typ; init_expr=Option.map ef init_expr }, slot)
  | Bound_frame (num_variables, body) ->
    location, Bound_frame (num_variables, sf body)
  | Compound statements ->
    location, Compound (List.map sf statements)
  | Declaration ({ typ; init_expr; _ } as decl) ->
    location, Declaration { decl with typ = map_const_type_children ef tf typ; init_expr=Option.map ef init_expr }
  | Do_while (body, cond) ->
    location, Do_while (sf body, ef cond)
  | Expression expr ->
    location, Expression (ef expr)
  | If (c, a, b) ->
    location, If (ef c, sf a, sf b)
  | Order_independent statements ->
    location, Order_independent (List.map sf statements)
  | Return expr ->
    location, Return (ef expr)

(* Map only the child statements and expressions of a expression node.
   The current expression node is reconstructed from the mapped children.
   This function does not invoke ef on the current node itself, preserving
   the child-only traversal invariant.
*)
let map_expression_children (sf : statement -> statement) (ef : expression -> expression) (tf : const_type_expression -> const_type_expression) ((location, expr) : expression) : expression =
  match expr with
  | Bool_literal _
  | Bound_identifier _
  | Bound_let _
  | Identifier _
  | Int_literal _
  | Let _ ->
    location, expr

  | Arity e ->
    location, Arity (ef e)
  | Assignment (a, b) ->
    location, Assignment (ef a, ef b)
  | Binary_op (op, a, b) ->
    location, Binary_op (op, ef a, ef b)
  | Call (callable, arg_exprs, pure) ->
    location, Call (ef callable, List.map ef arg_exprs, pure)
  | Conditional (c, a, b) ->
    location, Conditional (ef c, ef a, ef b)
  | Dynamic_array (es, t) ->
    location, Dynamic_array (Array.map ef es, map_const_type_children ef tf t)
  | Fall_through (a, b) ->
    location, Fall_through (ef a, ef b)
  | In (a, b) ->
    location, In (ef a, ef b)
  | Index (a, b) ->
    location, Index (ef a, Option.map ef b)
  | Lambda (return_type, params, modifiers, statement) ->
    location, Lambda (map_const_type_children ef tf return_type, List.map (map_statement_children sf ef tf) params, modifiers, sf statement)
  | Match (a, b, c, d, s) ->
    location, Match (ef a, ef b, ef c, ef d, s)
  | Statement s ->
    location, Statement (sf s)
  | Type t ->
    location, Type (tf t)
  | Type_of e ->
    location, Type_of (ef e)
  | Tuple es ->
    location, Tuple (List.map ef es)
  | Unary_op (op, a) ->
    location, Unary_op (op, ef a)
  
(* Map statement nodes with a full traversal. All nodes in the tree, including the one passed to map_statement, are transformed.
*)
let rec map_statement (sf : statement -> statement) (ef : expression -> expression) (tf : const_type_expression -> const_type_expression) (stmt : statement) : statement =
  sf (map_statement_children (map_statement sf ef tf) (map_expression sf ef tf) tf stmt)

(* Map expression nodes with a full traversal. All nodes in the tree, including the one passed to map_statement, are transformed.
*)
and map_expression (sf : statement -> statement) (ef : expression -> expression) (tf : const_type_expression -> const_type_expression) (expr : expression) : expression =
  ef (map_expression_children (map_statement sf ef tf) (map_expression sf ef tf) tf expr)