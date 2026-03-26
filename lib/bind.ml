open Ast
open Error
open Location
open Slot

module StringMap = Map.Make(String)

type bind_pass =
  | Order_dependent
  | Order_independent1
  | Order_independent2

type env = {
  (* The int associated with a value in the slots map is the "scope", which counts the level of lexical nesting.
  In contrast, the depth associated with the slot itself counts the level of _frame_ nesting. *)
  slots: (int*slot) StringMap.t;
  scope: int;
  frame: int;
  num_slots: int ref;
}

exception Redeclaration_error of location * string
exception Unbound_identifier_error of location * string

let error_redeclaration name = Error (Printf.sprintf "redeclaration of identifier '%s'" name)
let error_unbound_identifier name = Error (Printf.sprintf "unbound identifier '%s'" name)

let top_scope () : env = { slots=StringMap.empty; scope=0; frame=0; num_slots=ref 0 }
let new_scope env : env = { env with scope=env.scope+1 }
let new_frame env : env = { env with scope=env.scope+1; frame=env.frame+1; num_slots=ref 0 }

let new_slot env mut : slot =
  env.num_slots := 1 + !(env.num_slots);
  { index = !(env.num_slots) - 1; depth = env.frame; mut }

let find_slot (env : env) (name : string) : slot =
  let _, slot = StringMap.find name env.slots in slot

let add_slot (env : env) (name : string) (slot : slot) : env =
  { env with slots=StringMap.add name (env.scope, slot) env.slots }

let declare_slot (env : env) (name : string) (mut : bool) : env * slot =
  let slot = new_slot env mut in
  match StringMap.find_opt name env.slots with
  | Some (existing_scope, _) when existing_scope = env.scope -> raise (error_redeclaration name)
  | _ -> (add_slot env name slot), slot

let lookup_slot (env : env) (name : string) : slot =
  try
    find_slot env name
  with
  | Not_found -> raise (error_unbound_identifier name)
let num_env_slots (env: env) : int = !(env.num_slots)

let rec bind_order_dependent env = bind_statements env Order_dependent

and bind_order_independent env statements =
  let env, statements = bind_statements env Order_independent1 statements in
  bind_statements env Order_independent2 statements

and bind_statements (env: env) (pass : bind_pass) = function
  | [] -> env, []
  | h::t -> let env, h = bind_statement env pass h in let env, t = bind_statements env pass t in env, h::t

and bind_statement (env : env) (pass : bind_pass) ((location, statement) : statement) : env * statement =
  try
    match statement with
    | Declaration { modifiers=modifiers; name=name; typ; init_expr=init_expr } ->
      assert (pass != Order_independent2);
      let typ = bind_const_type env pass typ in
      let _, init_expr = bind_opt env pass init_expr in
      let env, slot = declare_slot env name modifiers.mut in
      env, (location, Bound_declaration ({ modifiers=modifiers; name=name; typ; init_expr=init_expr }, slot))

    | Bound_declaration ({ modifiers=modifiers; name=name; typ=typ; init_expr=init_expr }, slot) ->
      let typ = bind_const_type env pass typ in
      let _, init_expr = bind_opt env pass init_expr in
      env, (location, Bound_declaration ({ modifiers=modifiers; name=name; typ; init_expr=init_expr }, slot))

    | Expression expr ->
      let env, expr = bind env pass expr in env, (location, Expression expr)

    | Compound statements -> if pass == Order_independent1 then env, (location, statement) else
      let _, statements = bind_order_dependent (new_scope env) statements in env, (location, Compound statements)

    | Order_independent statements -> if pass == Order_independent1 then env, (location, statement) else
      let _, statements = bind_order_independent (new_scope env) statements in env, (location, Order_independent statements)

    | If (c, a, b) ->
      let _, c = bind env pass c in
      let _, a = bind_statement env pass a in
      let _, b = bind_statement env pass b in
      env, (location, If (c, a, b))

    | Do_while (body, cond) ->
      let _, body = bind_statement env pass body in
      let _, cond = bind env pass cond in
      env, (location, Do_while (body, cond))

    | Return expr ->
      let _, expr = bind env pass expr in env, (location, Return expr)

    | Bound_frame _ -> assert false
  with
    Error message -> raise (Located_error (location, message))
  
and bind_switch_cases env pass cases =
  List.map (fun (location, pattern, condition, stat) ->
    let env, pattern = bind_opt env pass pattern in
    let _, condition = bind_opt env pass condition in
    let _, stat = bind_statement env pass stat in
    (location, pattern, condition, stat)) cases

and bind_opt env pass (expr : expression option) : env * expression option =
  match expr with
  | Some expr ->
    let env, expr = bind env pass expr in env, Some expr
  | None -> env, None

and bind env pass ((location, expr) : expression) : env * expression =
  match expr with
  | Bool_literal _
  | Bound_identifier _
  | Bound_let _
  | Int_literal _
  | Type _
         -> env, (location, expr)
  
  | Assignment (a, b) ->
    let _, b = bind env pass b in
    let env, a = bind env pass a in
    env, (location, Assignment (a, b))
  
  | Let Identifier name ->
    assert (pass != Order_independent2);
    let env, slot = declare_slot env name false in
    env, (location, Bound_let (Identifier name, slot))

  | In (a, b) ->
    if pass == Order_independent1 then env, (location, expr) else
    let in_env, a = bind env Order_dependent a in
    let _, b = bind in_env Order_dependent b in
    env, (location, In (a, b))

  | Match (a, b, c, d, _) ->
    if pass == Order_independent1 then env, (location, expr) else
    let in_env, a = bind env Order_dependent a in
    let _, b = bind env Order_dependent b in
    let _, c = bind in_env Order_dependent c in
    let _, d = bind in_env Order_dependent d in
    env, (location, Match (a, b, c, d, new_slot in_env false))

  | Let Any ->
    assert (pass != Order_independent2);
    env, (location, Bound_let (Any, unbindable_slot))

  | Fall_through (a, b) ->
    let _, a = bind env pass a in
    let _, b = bind env pass b in
    env, (location, Fall_through (a, b))

  | Identifier name ->
    if pass == Order_independent1 then env, (location, expr) else
    let slot = lookup_slot env name in
    env, (location, Bound_identifier (name, slot))

  | Binary_op (op, a, b) ->
    let _, a = bind env pass a in
    let _, b = bind env pass b in
    env, (location, Binary_op (op, a, b))

  | Unary_op (op, a) ->
    let _, a = bind env pass a in
    env, (location, Unary_op (op, a))
  | Conditional (c, a, b) ->
    let _, c = bind env pass c in
    let _, a = bind env pass a in
    let _, b = bind env pass b in
    env, (location, Conditional (c, a, b))

  | Tuple es ->
    (* All BoundLets in the tuple must be added to the surrounding environment *)
    let env, es = List.fold_left (fun (env, es) e -> let env, e = bind env pass e in (env, e::es)) (env, []) es in
    env, (location, Tuple (List.rev es))

  | Type_of e ->
    let _, e = bind env pass e in
    env, (location, Type_of e)

  | Arity e ->
    let _, e = bind env pass e in
    env, (location, Arity e)
    
  | Lambda (return_type, params, modifiers, statement) ->
    let return_type = bind_const_type env pass return_type in
    if pass == Order_independent1 then env, (location, expr) else
    let frame_env = new_frame env in
    let frame_env, params = bind_order_dependent frame_env params in
    let _, statement = bind_statement (new_scope frame_env) Order_dependent statement in
    env, (location, Lambda (return_type, params, modifiers, (location, Bound_frame (!(frame_env.num_slots), statement))))

  | Call (callable, arg_exprs, pure) ->
    let _, callable = bind env pass callable in
    let arg_exprs = bind_expressions env pass arg_exprs in
    env, (location, Call (callable, arg_exprs, pure))

  | Dynamic_array (es, t) ->
    let es = Array.map (fun e -> let _, e = bind env pass e in e) es in
    let t = bind_const_type env pass t in
    env, (location, Dynamic_array (es, t))

  | Index (a, b) ->
    let _, a = bind env pass a in
    let _, b = bind_opt env pass b in
    env, (location, Index (a, b))

  | Statement s ->
    let _, s = bind_statement env pass s in
    env, (location, Statement s)

and bind_const_type env pass const_type =
  match const_type with
  | Unevaluated type_expr ->
    let _, type_expr = bind env pass type_expr in
    Unevaluated type_expr
  | _ -> const_type

and bind_expressions env pass exprs =
  List.map (fun expr -> let _, expr = bind env pass expr in expr) exprs

let bind_program (env : env) (statement : statement) : int * statement =
  let _, statement = bind_statement env Order_dependent statement in
  !(env.num_slots), statement