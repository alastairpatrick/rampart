open Location
open Sexplib
open Sexplib.Std
open Slot

type external_value = ..

let external_value_of_sexp _ : external_value = assert false
let sexp_of_external_value _ : Sexp.t = Sexp.Atom "External"
let pp_external_value _ _ = ()

type binary_op = Plus | Minus | Times | Div | Equals | NotEquals | Less | Greater

and unary_op = Minus

and pattern =
  | Any
  | Identifier of string

and ast_type =
  | Int
  | Bool
  | Void
  | Type

and expression_inner =
  | Type of ast_type
  | TypeOf of expression
  | Arity of expression
  | IntLiteral of int
  | BoolLiteral of bool
  | Assignment of expression * expression
  | Let of pattern
  | In of expression * expression
  | Identifier of string
  | BoundIdentifier of string * slot
  | BoundLet of pattern * slot
  | BinaryOp of binary_op * expression * expression
  | UnaryOp of unary_op * expression
  | Conditional of expression * expression * expression
  | Tuple of expression list
  | Call of expression * expression list
  | Lambda of (* return_type: *) expression * (* params: *) statement list * (* body: *) statement
  | External of external_value
  
and expression = location * expression_inner

and declaration = {
  type_expr: expression option;
  name: string;
  init_expr: expression option;
}

and switch_case = location * expression option * expression option * statement

and statement_inner =
  | Expression of expression
  | Declaration of declaration
  | BoundDeclaration of declaration * slot
  | BoundFrame of int * statement list
  | Compound of statement list
  | OrderIndependent of statement list
  | If of expression * (* then: *) statement * (* else: *) statement
  | DoWhile of statement * expression
  | Switch of expression * switch_case list
  | Return of expression option
  | AllocLocals of int * int

and statement = location * statement_inner

[@@deriving sexp, show]

let loc ((s: Lexing.position), (e: Lexing.position)) : location = make_location s e

let expression_location (l, _) = l
let statement_location (l, _) = l

let sexp_of_statements = [%sexp_of: statement list]

let show_statements = [%show: statement list]

let print_statements stats =
  Sexplib.Sexp.output_hum stdout (sexp_of_statements stats);
  flush stdout

let make_tuple_node (location : location) (exprs : expression list) : expression =
  match exprs with
  | [expr] -> expr
  | _ -> location, Tuple exprs