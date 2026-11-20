open Location
open Slot

module StringMap = Map.Make(String)

type bind_mode = {
  let_valid: bool;  (* whether a 'let' declaration is valid in this context *)
  assignable: bool;  (* whether the expression is on the left hand side of an assignment *)
}

type env = {
  (* The int associated with a value in the slots map counts the level of lexical nesting.
  In contrast, the depth associated with the slot itself counts the level of _frame_ nesting. *)
  slots: (int * slot) StringMap.t;
  scope: int;
  frame: int;
  num_slots: int;
  diagnostic : (Diagnostic.diagnostic_type -> location -> string -> unit)
}

let top_scope diagnostic : env = { slots=StringMap.empty; scope=0; frame=0; num_slots=0; diagnostic }
let new_scope env : env = { env with scope=env.scope+1 }
let new_frame env : env = { env with scope=env.scope+1; frame=env.frame+1; num_slots=0 }

let new_slot env mut : env * slot =
  { env with num_slots=env.num_slots+1 }, { index = env.num_slots; depth = env.frame; mut }

let find_slot (env : env) (name : string) : slot option =
  match StringMap.find_opt name env.slots with
  | Some (_, slot) -> Some slot
  | _ -> None

let add_slot (env : env) (name : string) (slot : slot) : env =
  { env with slots=StringMap.add name (env.scope, slot) env.slots }

let declare_slot (env : env) (name : string) (mut : bool) : (env * slot) option =
  match StringMap.find_opt name env.slots with
  | Some (scope, _) when scope = env.scope -> None
  | _ ->
      let env, slot = new_slot env mut in
      Some (add_slot env name slot, slot)

let num_env_slots (env: env) : int = env.num_slots

let rec bind_statements env (ss : Ast.stat list) : env * Ast.stat list =
  match ss with
  | [] -> env, []
  | s::rest ->
    let env, s = bind_statement env s in
    let env, rest = bind_statements env rest in
    env, s :: rest

and bind_statement env { u; loc } : env * Ast.stat =
  match u with
  | Ast.Expr e ->
    let env, e = bind_expression env {let_valid=true; assignable=false} e in
    env, { u = Ast.Expr e; loc }
  | Ast.Compound ss ->
    let _, ss = bind_statements (new_scope env) ss in
    env, { u = Ast.Compound ss; loc }
  | Ast.Conditional (cond, cons, alt) ->
    let _, cond = bind_expression env {let_valid=false; assignable=false} cond in
    let _, cons = bind_statement env cons in
    let _, alt = bind_statement env alt in
    env, { u = Ast.Conditional (cond, cons, alt); loc }

and bind_parameters env (params: Ast.parameter list) : env * Ast.parameter list =
  match params with
  | [] -> env, []
  | (loc, id, typ)::rest ->
    let typ = bind_type env typ in
    let env = match declare_slot env id false with
      | Some (env, _) ->
        env
      | None ->
        env.diagnostic Diagnostic.Error loc (Printf.sprintf "Parameter '%s' redeclared" id);
        env
    in
    let env, rest = bind_parameters env rest in
    env, (loc, id, typ) :: rest

and bind_expression env (mode : bind_mode) { typ; loc; u } : env * Ast.expr =
  match u with
  | Ast.Bool _
  | Ast.Int _
  | BoundIdentifier _
  | BoundLet _ ->
    env, { typ; loc; u }
  | Identifier id ->
    (match find_slot env id with
    | Some slot -> env, { typ; loc; u = Ast.BoundIdentifier (id, slot) }
    | None ->
      env.diagnostic Diagnostic.Error loc (Printf.sprintf "Identifier '%s' not found" id);
      env, { typ; loc; u = Ast.BoundIdentifier (id, unbindable_slot) }
    )
  | Let (id, mut) ->
    if not mode.let_valid then
      (env.diagnostic Diagnostic.Error loc (Printf.sprintf "Declaration of identifier '%s' is invalid in this context" id);
      env, { typ; loc; u = Ast.BoundLet (id, unbindable_slot) })
    else
      (match declare_slot env id mut with
      | Some (env, slot) -> env, { typ; loc; u = Ast.BoundLet (id, slot) }
      | None ->
        env.diagnostic Diagnostic.Error loc (Printf.sprintf "Identifier '%s' already declared in this scope" id);
        env, { typ; loc; u = Ast.BoundLet (id, unbindable_slot) }
      )
  | Convert (e, t) ->
    let env, e = bind_expression env mode e in
    let t = bind_type env t in
    env, { typ; loc; u = Ast.Convert (e, t) }
  | Tuple es ->
    let env, es = List.fold_left (fun (env, es) e ->
      let env, e = bind_expression env mode e in
      env, e::es
    ) (env, []) es in
    env, { typ; loc; u = Ast.Tuple (List.rev es) }
  | _ when mode.assignable ->
    env.diagnostic Diagnostic.Error loc "This expression may not appear on the left hand side of an assignment";
    env, { typ; loc; u }

  | Assignment (op, lhs, rhs) ->
    let lhs_env, lhs = bind_expression env {mode with assignable=true} lhs in
    let _, rhs = bind_expression env {let_valid=false; assignable=false} rhs in
    lhs_env, { typ; loc; u = Ast.Assignment (op, lhs, rhs) }
  | In (e1, e2) ->
    let in_env = new_scope env in
    let in_env, e1 = bind_expression in_env {let_valid=true; assignable=false} e1 in
    let _, e2 = bind_expression in_env {let_valid=false; assignable=false} e2 in
    env, { typ; loc; u = Ast.In (e1, e2) }
  | BinOp (op, a, b) ->
    let _, a = bind_expression env {let_valid=false; assignable=false} a in
    let _, b = bind_expression env {let_valid=false; assignable=false} b in
    env, { typ; loc; u = Ast.BinOp (op, a, b) }
  | UnOp (op, e) ->
    let _, e = bind_expression env {let_valid=false; assignable=false} e in
    env, { typ; loc; u = Ast.UnOp (op, e) }
  | Function (params, ret, body) ->
    let ret = Option.map (bind_type env) ret in
    let new_env = new_frame env in
    let new_env, params = bind_parameters new_env params in
    let _, body = bind_statement new_env body in
    env, { typ; loc; u = Ast.Function (params, ret, body) }
  | Call (f, args) ->
    let _, f = bind_expression env {let_valid=false; assignable=false} f in
    let _, args = List.fold_left (fun (env, args) arg ->
      let _, arg = bind_expression env {let_valid=false; assignable=false} arg in
      env, arg::args
    ) (env, []) args in
    env, { typ; loc; u = Ast.Call (f, List.rev args) }

and bind_type env typ : Ast.typ =
  match typ with
  | Ast.BoolT
  | Ast.IntT _
  | Ast.UIntT _ ->
    typ
  | Ast.TupleT ts -> Ast.TupleT (List.map (bind_type env) ts)
  | Ast.FunctionT (params, ret) ->
    let params = List.map (fun t -> bind_type env t) params in
    let ret = bind_type env ret in
    Ast.FunctionT (params, ret)
  