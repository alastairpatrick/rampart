open Location
open Sexplib.Std
open Slot

type external_closure = ..

type binary_op =
  | Plus
  | Minus
  | Times
  | Div
  | Modulo
  | Equals
  | Not_equals
  | Less
  | Less_equals
  | Greater
  | Greater_equals
  | Logical_and (* operands must be bool, can short-circuit *)
  | Logical_or (* operands must be bool, can short-circuit *)
  | Bitwise_and (* int or bool operands *)
  | Bitwise_or (* int or bool operands *)
  | Bitwise_xor (* int or bool operands *)
  | Shift_left   (* int operands only, C "<<" *)
  | Shift_right  (* int operands only, C ">>"; arithmetic shift like Java *)

and unary_op =
  | Negate (* int operand *)
  | Logical_not (* bool operand *)
  | Bitwise_invert (* int or bool operand *)

and pattern =
  | Any
  | Identifier of string

and function_modifiers = {
  pure: bool [@sexp.bool];
  const: bool [@sexp.bool];
}

and const_type_expression =
  | Bool
  | Deduced
  | Dynamic_array of (* element_type: *) const_type_expression
  | Int
  | Function of (* return_type: *) const_type_expression * (* param_types: *) const_type_expression list * (* modifiers: *) function_modifiers
  | Opaque (* (Pointer Opaque) roughly corresponds to void* in C *)
  | Pointer of const_type_expression
  | Representative (* Uninstantiable type, used as a representative value for type values. *)
  | Tuple of const_type_expression list
  | Unevaluated of expression (* Represents types before they are evaluated to actual const_type values. *)
  | Type

and expression_inner =
  | Arity of expression
  | Assignment of expression * expression
  | Binary_op of binary_op * expression * expression
  | Bool_literal of bool
  | Bound_identifier of string * slot
  | Bound_let of pattern * slot
  | Call of expression * expression list * function_modifiers
  | Conditional of expression * expression * expression
  | Dynamic_array of expression array * (* element_type: *) const_type_expression
  | Fall_through of expression * expression
  | Identifier of string
  | Index of expression * (* subscript: *) expression option
  | In of expression * expression
  | Int_literal of int64
  | Lambda of (* return_type: *) const_type_expression * (* params: *) statement list * function_modifiers * (* body: *) statement
  | Let of pattern
  | Match of (* pattern: *) expression * expression * (* condition: *) expression * (* body: *) expression * (* temp_slot: *) slot
  | Statement of statement
  | Tuple of expression list
  | Type of const_type_expression
  | Type_of of expression
  | Unary_op of unary_op * expression
  
and expression = location * expression_inner

and declaration_modifiers = {
  mut: bool [@sexp.bool];
}

and declaration = {
  modifiers: declaration_modifiers;
  typ: const_type_expression;
  name: string;
  init_expr: expression option;
}

and switch_case = location * expression option * expression option * statement

and statement_inner =
  | Expression of expression
  | Declaration of declaration
  | Bound_declaration of declaration * slot
  | Bound_frame of int * statement
  | Compound of statement list
  | Order_independent of statement list
  | If of expression * (* then: *) statement * (* else: *) statement
  | Do_while of statement * expression
  | Return of expression

and statement = location * statement_inner

[@@deriving sexp, show]

let empty_declaration_modifiers : declaration_modifiers = { mut = false }
let empty_function_modifiers : function_modifiers = { pure = false; const = false }

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
  | Not_equals -> "!="
  | Less -> "<"
  | Less_equals -> "<="
  | Greater -> ">"
  | Greater_equals -> ">="
  | Logical_and -> "&&"
  | Logical_or -> "||"
  | Bitwise_and -> "band"
  | Bitwise_or -> "bor"
  | Bitwise_xor -> "bxor"
  | Shift_left -> "<<"
  | Shift_right -> ">>"

let show_unary_op = function
  | Negate -> "-"
  | Logical_not -> "!"
  | Bitwise_invert -> "bnot"