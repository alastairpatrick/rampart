open Ast
    
let rec map_statement (sf : statement -> statement) (ef : expression -> expression) ((location, statement) : statement) : statement =
  match statement with
  | Declaration { modifiers=modifiers; name=name; typ; init_expr=init_expr } ->
    sf (location, Declaration { modifiers=modifiers; name=name; typ=map_const_type sf ef typ; init_expr=Option.map (map_expression sf ef) init_expr })

  | Bound_declaration ({ modifiers=modifiers; name=name; typ=typ; init_expr=init_expr }, slot) ->
    let typ = match typ with
    | Unevaluated type_expr -> Unevaluated (map_expression sf ef type_expr)
    | _ -> typ in
    sf (location, Bound_declaration ({ modifiers=modifiers; name=name; typ; init_expr=Option.map (map_expression sf ef) init_expr }, slot))

  | Expression expr ->
    sf (location, Expression (map_expression sf ef expr))

  | Compound statements ->
    let statements = List.map (map_statement sf ef) statements in sf (location, Compound statements)

  | Order_independent statements ->
    let statements = List.map (map_statement sf ef) statements in sf (location, Order_independent statements)

  | If (c, a, b) ->
    sf (location, If (map_expression sf ef c, map_statement sf ef a, map_statement sf ef b))

  | Do_while (body, cond) ->
    sf (location, Do_while (map_statement sf ef body, map_expression sf ef cond))

  | Return expr ->
    sf (location, Return (map_expression sf ef expr))

  | Bound_frame (num_variables, body) ->
    sf (location, Bound_frame (num_variables, map_statement sf ef body))

and map_expression (sf : statement -> statement) (ef : expression -> expression) ((location, expr) : expression) : expression =
  match expr with
  | Bool_literal _
  | Bound_identifier _
  | Bound_let _
  | Identifier _
  | Int_literal _
  | Let Any
  | Let Identifier _
  | Type _ ->
    ef (location, expr)
  
  | Assignment (a, b) ->
    ef (location, (Assignment (map_expression sf ef a, map_expression sf ef b)))

  | In (a, b) ->
    ef (location, (In (map_expression sf ef a, map_expression sf ef b)))

  | Binary_op (op, a, b) ->
    ef (location, (Binary_op (op, map_expression sf ef a, map_expression sf ef b)))

  | Unary_op (op, a) ->
    ef (location, (Unary_op (op, map_expression sf ef a)))
  | Conditional (c, a, b) ->
    ef (location, (Conditional (map_expression sf ef c, map_expression sf ef a, map_expression sf ef b)))

  | Tuple es ->
    ef (location, (Tuple (List.map (map_expression sf ef) es)))

  | Type_of e ->
    ef (location, (Type_of (map_expression sf ef e)))

  | Arity e ->
    ef (location, (Arity (map_expression sf ef e)))

  | Lambda (return_type, params, modifiers, statement) ->
    ef (location, (Lambda (map_const_type sf ef return_type, List.map (map_statement sf ef) params, modifiers, map_statement sf ef statement)))

  | Call (callable, arg_exprs, pure) ->
    ef (location, (Call (map_expression sf ef callable, List.map (map_expression sf ef) arg_exprs, pure)))

  | Dynamic_array (es, t) ->
    ef (location, (Dynamic_array (Array.map (map_expression sf ef) es, map_const_type sf ef t)))
  | Index (a, b) ->
    ef (location, (Index (map_expression sf ef a, Option.map (map_expression sf ef) b)))

  | Fall_through (a, b) ->
    ef (location, (Fall_through (map_expression sf ef a, map_expression sf ef b)))

  | Match (a, b, c, d, s) ->
    ef (location, (Match (map_expression sf ef a, map_expression sf ef b, map_expression sf ef c, map_expression sf ef d, s)))

  | Statement s ->
    ef (location, Statement (map_statement sf ef s))
    
and map_const_type (sf : statement -> statement) (ef : expression -> expression) (const_type : const_type_expression) : const_type_expression =
  match const_type with
  | Unevaluated type_expr -> Unevaluated (map_expression sf ef type_expr)
  | _ -> const_type

let reduce_statement (sf : 'acc -> statement -> 'acc) (ef : 'acc -> expression -> 'acc) (acc : 'acc) (stmt : statement) : 'acc =
  let acc = ref acc in
  map_statement (fun s -> acc := sf !acc s; s) (fun e -> acc := ef !acc e; e) stmt |> ignore;
  !acc

let reduce_expression (sf : 'acc -> statement -> 'acc) (ef : 'acc -> expression -> 'acc) (acc : 'acc) (expr : expression) : 'acc =
  let acc = ref acc in
  map_expression (fun s -> acc := sf !acc s; s) (fun e -> acc := ef !acc e; e) expr |> ignore;
  !acc
  
let reduce_map_expression (sf : 'acc -> statement -> 'acc * statement) (ef : 'acc -> expression -> 'acc * expression) (acc : 'acc) (expr : expression) : 'acc * expression =
  let acc = ref acc in
  let expr = map_expression (fun s -> let s = sf !acc s in acc := fst s; snd s) (fun e -> let e = ef !acc e in acc := fst e; snd e) expr in
  !acc, expr

let reduce_map_statement (sf : 'acc -> statement -> 'acc * statement) (ef : 'acc -> expression -> 'acc * expression) (acc : 'acc) (stmt : statement) : 'acc * statement =
  let acc = ref acc in
  let stmt = map_statement (fun s -> let s = sf !acc s in acc := fst s; snd s) (fun e -> let e = ef !acc e in acc := fst e; snd e) stmt in
  !acc, stmt
