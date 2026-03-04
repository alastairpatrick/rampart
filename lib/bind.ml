open Ast
open Error
open Location
open Slot

module StringMap = Map.Make(String)

type bind_pass =
  | OrderDependent
  | OrderIndependent1
  | OrderIndependent2

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

let new_slot env : slot =
  env.num_slots := 1 + !(env.num_slots);
  { index = !(env.num_slots) - 1; depth = env.frame }

let find_slot (env : env) (name : string) : slot =
  let _, slot = StringMap.find name env.slots in slot

let add_slot (env : env) (name : string) (slot : slot) : env =
  { env with slots=StringMap.add name (env.scope, slot) env.slots }

let declare_slot (env : env) (name : string) : env * slot =
  let slot = new_slot env in
  match StringMap.find_opt name env.slots with
  | Some (existing_scope, _) when existing_scope = env.scope -> raise (error_redeclaration name)
  | _ -> (add_slot env name slot), slot

let lookup_slot (env : env) (name : string) : slot =
  try
    find_slot env name
  with
  | Not_found -> raise (error_unbound_identifier name)
let num_env_slots (env: env) : int = !(env.num_slots)

let rec bind_order_dependent env = bind_statements env OrderDependent

and bind_order_independent env statements =
  let env, statements = bind_statements env OrderIndependent1 statements in
  bind_statements env OrderIndependent2 statements

and bind_statements (env: env) (pass : bind_pass) = function
  | [] -> env, []
  | h::t -> let env, h = bind_statement env pass h in let env, t = bind_statements env pass t in env, h::t

and bind_statement (env : env) (pass : bind_pass) ((location, statement) : statement) : env * statement =
  try
    match statement with
    | Declaration { modifiers=modifiers; name=name; type_expr=type_expr; init_expr=init_expr } ->
      assert (pass != OrderIndependent2);
      let _, type_expr = bind_opt env pass type_expr in
      let _, init_expr = bind_opt env pass init_expr in
      let env, slot = declare_slot env name in
      env, (location, BoundDeclaration ({ modifiers=modifiers; name=name; type_expr=type_expr; init_expr=init_expr }, slot))

    | BoundDeclaration ({ modifiers=modifiers; name=name; type_expr=type_expr; init_expr=init_expr }, slot) ->
      let _, type_expr = bind_opt env pass type_expr in
      let _, init_expr = bind_opt env pass init_expr in
      env, (location, BoundDeclaration ({ modifiers=modifiers; name=name; type_expr=type_expr; init_expr=init_expr }, slot))

    | Expression expr ->
      let env, expr = bind env pass expr in env, (location, Expression expr)

    | Compound statements -> if pass == OrderIndependent1 then env, (location, statement) else
      let _, statements = bind_order_dependent (new_scope env) statements in env, (location, Compound statements)

    | OrderIndependent statements -> if pass == OrderIndependent1 then env, (location, statement) else
      let _, statements = bind_order_independent (new_scope env) statements in env, (location, OrderIndependent statements)

    | If (c, a, b) ->
      let _, c = bind env pass c in
      let _, a = bind_statement env pass a in
      let _, b = bind_statement env pass b in
      env, (location, If (c, a, b))

    | DoWhile (body, cond) ->
      let _, body = bind_statement env pass body in
      let _, cond = bind env pass cond in
      env, (location, DoWhile (body, cond))

    | Switch (expr, cases) ->
      let _, expr = bind env pass expr in
      let cases = bind_switch_cases env pass cases in
      env, (location, Switch (expr, cases))

    | Return None -> env, (location, Return None)

    | Return Some expr ->
      let _, expr = bind env pass expr in env, (location, Return (Some expr))

    | BoundFrame _

    | AllocLocals _ -> assert false
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

and alloc_locals env arity statements = 
  if !(env.num_slots) = 0 then statements else
  (null_location, AllocLocals (!(env.num_slots), arity)) :: statements

and bind env pass ((location, expr) : expression) : env * expression =
  match expr with
  | BoolLiteral _
  | BoundIdentifier _
  | BoundLet _
  | IntLiteral _
  | Type _
         -> env, (location, expr)
  
  | Assignment (a, b) ->
    let _, b = bind env pass b in
    let env, a = bind env pass a in
    env, (location, Assignment (a, b))
  
  | Let Identifier name ->
    assert (pass != OrderIndependent2);
    let env, slot = declare_slot env name in
    env, (location, BoundLet (Identifier name, slot))

  | In (a, b) ->
    if pass == OrderIndependent1 then env, (location, expr) else
    let in_env, a = bind env OrderDependent a in
    let _, b = bind in_env OrderDependent b in
    env, (location, In (a, b))

  | Let Any ->
    assert (pass != OrderIndependent2);
    env, (location, BoundLet (Any, new_slot env))

  | Identifier name ->
    if pass == OrderIndependent1 then env, (location, expr) else
    let slot_ref = lookup_slot env name in
    env, (location, BoundIdentifier (name, slot_ref))

  | BinaryOp (op, a, b) ->
    let _, a = bind env pass a in
    let _, b = bind env pass b in
    env, (location, BinaryOp (op, a, b))

  | UnaryOp (op, a) ->
    let _, a = bind env pass a in
    env, (location, UnaryOp (op, a))

  | Conditional (c, a, b) ->
    let _, c = bind env pass c in
    let _, a = bind env pass a in
    let _, b = bind env pass b in
    env, (location, Conditional (c, a, b))

  | Tuple es ->
    (* All BoundLets in the tuple must be added to the surrounding environment *)
    let env, es = List.fold_left (fun (env, es) e -> let env, e = bind env pass e in (env, e::es)) (env, []) es in
    env, (location, Tuple (List.rev es))

  | TypeOf e ->
    let _, e = bind env pass e in
    env, (location, TypeOf e)

  | Arity e ->
    let _, e = bind env pass e in
    env, (location, Arity e)
    
  | Lambda (return_type, params, modifiers, (_, Compound statements), _) ->
    let _, return_type = bind env pass return_type in
    if pass == OrderIndependent1 then env, (location, expr) else
    let frame_env = new_frame env in
    let frame_env, params = bind_order_dependent frame_env params in
    let _, statements = bind_order_dependent (new_scope frame_env) statements in
    env, (location, Lambda (return_type, params, modifiers, (location, BoundFrame (!(frame_env.num_slots), statements)), None))

  | Lambda _ -> assert false

  | Call (callable, arg_exprs, pure) ->
    let _, callable = bind env pass callable in
    let arg_exprs = bind_expressions env pass arg_exprs in
    env, (location, Call (callable, arg_exprs, pure))
  
and bind_expressions env pass exprs =
  List.map (fun expr -> let _, expr = bind env pass expr in expr) exprs

let bind_program (env : env) (statement : statement) : int * statement =
  let _, statement = bind_statement env OrderDependent statement in
  !(env.num_slots), statement