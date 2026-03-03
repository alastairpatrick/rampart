open Location
open Sexplib
open Sexplib.Std
open Slot

type expression_annotation = ..

let expression_annotation_of_sexp _ : expression_annotation = assert false
let sexp_of_expression_annotation _ : Sexp.t = Sexp.Atom "External"
let pp_expression_annotation _ _ = ()

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

and lambda_modifiers = {
  pure: bool [@sexp.bool];
  const: bool [@sexp.bool];
}

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
  | Call of expression * expression list * (* pure: *) bool
  | Lambda of (* return_type: *) expression * (* params: *) statement list * lambda_modifiers * (* body: *) statement
  | Annotated of expression_annotation * expression
  
and expression = location * expression_inner

and declaration_modifiers = {
  mut: bool [@sexp.bool];
}

and declaration = {
  modifiers: declaration_modifiers;
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

let empty_declaration_modifiers : declaration_modifiers = { mut = false }
let empty_lambda_modifiers : lambda_modifiers = { pure = false; const = false }

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

let show_binary_op = function
  | Plus -> "+"
  | Minus -> "-"
  | Times -> "*"
  | Div -> "/"
  | Equals -> "=="
  | NotEquals -> "!="
  | Less -> "<"
  | Greater -> ">"