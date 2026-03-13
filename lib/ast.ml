open Location
open Sexplib
open Sexplib.Std
open Slot

type external_closure = ..

type closure = (* identity: *) int * external_closure

let closure_of_sexp _ : closure = assert false
let sexp_of_closure (identity, _) : Sexp.t = Sexp.Atom (string_of_int identity)
let pp_closure _ _ = ()

type binary_op =
  | Plus
  | Minus
  | Times
  | Div
  | Modulo
  | Equals
  | NotEquals
  | Less
  | LessEquals
  | Greater
  | GreaterEquals
  | LogicalAnd (* operands must be bool, can short-circuit *)
  | LogicalOr (* operands must be bool, can short-circuit *)
  | BitwiseAnd (* int or bool operands *)
  | BitwiseOr (* int or bool operands *)
  | BitwiseXor (* int or bool operands *)
  | ShiftLeft   (* int operands only, C "<<" *)
  | ShiftRight  (* int operands only, C ">>"; arithmetic shift like Java *)

and unary_op =
  | Negate (* int operand *)
  | LogicalNot (* bool operand *)
  | BitwiseInvert (* int or bool operand *)

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
  | Call of expression * expression list * lambda_modifiers
  | Lambda of (* return_type: *) expression * (* params: *) statement list * lambda_modifiers * (* body: *) statement * closure option
  | DynamicArray of expression array * (* element_type: *) expression option
  | Index of expression * (* subscript: *) expression option
  
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
  | BoundFrame of int * statement
  | Compound of statement list
  | OrderIndependent of statement list
  | If of expression * (* then: *) statement * (* else: *) statement
  | DoWhile of statement * expression
  | Switch of expression * switch_case list
  | Return of expression

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
  | Modulo -> "%"
  | Div -> "/"
  | Equals -> "=="
  | NotEquals -> "!="
  | Less -> "<"
  | LessEquals -> "<="
  | Greater -> ">"
  | GreaterEquals -> ">="
  | LogicalAnd -> "&&"
  | LogicalOr -> "||"
  | BitwiseAnd -> "&"
  | BitwiseOr -> "|"
  | BitwiseXor -> "^"
  | ShiftLeft -> "<<"
  | ShiftRight -> ">>"

let show_unary_op = function
  | Negate -> "-"
  | LogicalNot -> "!"
  | BitwiseInvert -> "~"