open Location
open Slot

type typ =
  | BoolT
  | IntT of int
  | UIntT of int
  | TupleT of typ list
  | FunctionT of typ list * typ

and parameter = location * string * typ

and bin_op = Add | Subtract | Multiply | Divide
and un_op = Negate

and expr_variant =
  | Bool of bool
  | Int of int64
  | Assignment of bin_op option * expr * expr
  | Identifier of string
  | BoundIdentifier of string * slot
  | Let of string * bool
  | BoundLet of string * slot
  | In of expr * expr
  | Convert of expr * typ
  | Tuple of expr list
  | BinOp of bin_op * expr * expr
  | UnOp of un_op * expr
  | Function of parameter list * typ option * stat
  | Call of expr * expr list

and expr2 = {
  typ: typ;
  loc: location;
  u: expr_variant;
}

and expr = expr2 [@printer fun fmt (e: expr) -> pp_expr_variant fmt e.u]

and stat_variant =
  | Expr of expr
  | Compound of stat list
  | Conditional of expr * stat * stat

and stat2 = {
  loc: location;
  u: stat_variant;
}

and stat = stat2 [@printer fun fmt (s: stat) -> pp_stat_variant fmt s.u]
and file = stat list

[@@deriving show { with_path=false }]

let void_type = TupleT []
