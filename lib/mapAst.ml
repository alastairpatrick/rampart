open Ast
    
let rec map_statement (sf : statement -> statement) (ef : expression -> expression) ((location, statement) : statement) : statement =
  match statement with
  | Declaration { modifiers=modifiers; name=name; typ; init_expr=init_expr } ->
    sf (location, Declaration { modifiers=modifiers; name=name; typ=Option.map (map_const_type sf ef) typ; init_expr=Option.map (map_expression sf ef) init_expr })

  | BoundDeclaration ({ modifiers=modifiers; name=name; typ=typ; init_expr=init_expr }, slot) ->
    let typ = match typ with
    | None -> None
    | Some (Unevaluated_type type_expr) -> Some (Unevaluated_type (map_expression sf ef type_expr))
    | _ -> typ in
    sf (location, BoundDeclaration ({ modifiers=modifiers; name=name; typ; init_expr=Option.map (map_expression sf ef) init_expr }, slot))

  | Expression expr ->
    sf (location, Expression (map_expression sf ef expr))

  | Compound statements ->
    let statements = List.map (map_statement sf ef) statements in sf (location, Compound statements)

  | OrderIndependent statements ->
    let statements = List.map (map_statement sf ef) statements in sf (location, OrderIndependent statements)

  | If (c, a, b) ->
    sf (location, If (map_expression sf ef c, map_statement sf ef a, map_statement sf ef b))

  | DoWhile (body, cond) ->
    sf (location, DoWhile (map_statement sf ef body, map_expression sf ef cond))

  | Return expr ->
    sf (location, Return (map_expression sf ef expr))

  | BoundFrame (num_variables, body) ->
    sf (location, BoundFrame (num_variables, map_statement sf ef body))

and map_expression (sf : statement -> statement) (ef : expression -> expression) ((location, expr) : expression) : expression =
  match expr with
  | BoolLiteral _
  | BoundIdentifier _
  | BoundLet _
  | Identifier _
  | IntLiteral _
  | Let Any
  | Let Identifier _
  | Type _ ->
    ef (location, expr)
  
  | Assignment (a, b) ->
    ef (location, (Assignment (map_expression sf ef a, map_expression sf ef b)))

  | In (a, b) ->
    ef (location, (In (map_expression sf ef a, map_expression sf ef b)))

  | BinaryOp (op, a, b) ->
    ef (location, (BinaryOp (op, map_expression sf ef a, map_expression sf ef b)))

  | UnaryOp (op, a) ->
    ef (location, (UnaryOp (op, map_expression sf ef a)))

  | Conditional (c, a, b) ->
    ef (location, (Conditional (map_expression sf ef c, map_expression sf ef a, map_expression sf ef b)))

  | Tuple es ->
    ef (location, (Tuple (List.map (map_expression sf ef) es)))

  | TypeOf e ->
    ef (location, (TypeOf (map_expression sf ef e)))

  | Arity e ->
    ef (location, (Arity (map_expression sf ef e)))

  | Lambda (return_type, params, modifiers, statement, closure) ->
    ef (location, (Lambda (map_const_type sf ef return_type, List.map (map_statement sf ef) params, modifiers, map_statement sf ef statement, closure)))

  | Call (callable, arg_exprs, pure) ->
    ef (location, (Call (map_expression sf ef callable, List.map (map_expression sf ef) arg_exprs, pure)))

  | DynamicArray (es, t) ->
    ef (location, (DynamicArray (Array.map (map_expression sf ef) es, Option.map (map_const_type sf ef) t)))

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
  | Unevaluated_type type_expr -> Unevaluated_type (map_expression sf ef type_expr)
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
