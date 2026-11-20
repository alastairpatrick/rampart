type context = unit

let rec evaluate (ctx: context) (statements: Ast.stat list) : Ast.stat list =
  List.map (evaluate_statement ctx) statements

and evaluate_statement ctx {u; loc;} : Ast.stat =
  match u with
  | Ast.Expr e -> {u=Ast.Expr (evaluate_expression ctx e); loc}
  | _ -> failwith "Evaluation of this statement type is not implemented yet."

and evaluate_expression ctx {typ; loc; u} : Ast.expr =
  match u with
  | Ast.Int _ -> {typ; loc; u}
  | Ast.BinOp (op, left, right) -> evaluate_binary_operation ctx loc op left right
  | _ -> failwith "Evaluation of this AST node is not implemented yet."

and evaluate_binary_operation ctx loc op left right : Ast.expr =
  let left_val = evaluate_expression ctx left in
  let right_val = evaluate_expression ctx right in
  match (op, left_val, right_val) with
  | (Ast.Add, {u = Ast.Int l; _}, {u = Ast.Int r; _}) -> {Ast.typ = IntT 64; loc; u = Ast.Int (Int64.add l r)}
  | (Ast.Subtract, {u = Ast.Int l; _}, {u = Ast.Int r; _}) -> {Ast.typ = IntT 64; loc; u = Ast.Int (Int64.sub l r)}
  | (Ast.Multiply, {u = Ast.Int l; _}, {u = Ast.Int r; _}) -> {Ast.typ = IntT 64; loc; u = Ast.Int (Int64.mul l r)}
  | (Ast.Divide, {u = Ast.Int l; _}, {u = Ast.Int r; _}) ->
      if r = 0L then failwith "Division by zero"
      else {Ast.typ = IntT 64; loc; u = Ast.Int (Int64.div l r)}
  | _ -> failwith "Unsupported binary operation or operand types."  