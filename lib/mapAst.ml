open Ast

let traverse_const_type (ef : expression -> expression) (tf : const_type_expression -> const_type_expression) (typ: const_type_expression) : const_type_expression =
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

let traverse_statement (sf: statement -> statement) (ef : expression -> expression) (tf : const_type_expression -> const_type_expression) ((location, stmt): statement) : statement =
  match stmt with
  | Bound_declaration (({ typ; init_expr; _ } as decl), slot) ->
    location, Bound_declaration ({ decl with typ = traverse_const_type ef tf typ; init_expr=Option.map ef init_expr }, slot)
  | Bound_frame (num_variables, body) ->
    location, Bound_frame (num_variables, sf body)
  | Compound statements ->
    location, Compound (List.map sf statements)
  | Declaration ({ typ; init_expr; _ } as decl) ->
    location, Declaration { decl with typ = traverse_const_type ef tf typ; init_expr=Option.map ef init_expr }
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

let traverse_expression (sf : statement -> statement) (ef : expression -> expression) (tf : const_type_expression -> const_type_expression) ((location, expr) : expression) : expression =
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
    location, Dynamic_array (Array.map ef es, traverse_const_type ef tf t)
  | Fall_through (a, b) ->
    location, Fall_through (ef a, ef b)
  | In (a, b) ->
    location, In (ef a, ef b)
  | Index (a, b) ->
    location, Index (ef a, Option.map ef b)
  | Lambda (return_type, params, modifiers, statement) ->
    location, Lambda (traverse_const_type ef tf return_type, List.map (traverse_statement sf ef tf) params, modifiers, sf statement)
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
  
let rec map_statement (sf : statement -> statement) (ef : expression -> expression) (tf : const_type_expression -> const_type_expression) (stmt : statement) : statement =
  sf (traverse_statement (map_statement sf ef tf) (map_expression sf ef tf) tf stmt)

and map_expression (sf : statement -> statement) (ef : expression -> expression) (tf : const_type_expression -> const_type_expression) (expr : expression) : expression =
  ef (traverse_expression (map_statement sf ef tf) (map_expression sf ef tf) tf expr)