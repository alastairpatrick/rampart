open Ast
open Location

exception Located_error of location * string
exception Error of string
exception Saw_failed_error

let error_internal msg = Error (Printf.sprintf "internal error: %s" msg)
let error_not_assignable location = Located_error (location, "expression is not assignable")
(*let error_cyclic_dependency location names =
  Error (location, (sprintf "found cyclic dependency: %s" (String.concat ", " (StringSet.to_list names))))*)
let error_type_mismatch = Error "type mismatch"
let error_incorrect_number_of_arguments expected actual = Error (Printf.sprintf "expected %d arguments but got %d" expected actual)
let error_order_independent = Error "not allowed in an order independent context"
let error_not_a_type = Error "not a type"
let error_not_callable = Error "not callable"
let error_unassigned_let (pattern : pattern) =
  Error (match pattern with
    | Identifier name -> (Printf.sprintf "'let' introduces variable '%s' but it is not assigned a value" name)
    | Any -> "'let' expression is not assigned a value")
let error_cyclic_dependency (dependencies : string list) =
  Error (Printf.sprintf "cyclic dependencies detected: %s" (String.concat ", " dependencies))
let error_invalid_operation (message : string) = Error (Printf.sprintf "invalid operation: %s" message)
let error_immutable_assignment name = Error (Printf.sprintf "cannot assign to immutable variable '%s'" name)
let error_cannot_nest_impure_function_in_pure_context = Error "cannot nest impure function in pure context"
let error_cannot_call_impure_function_from_pure_context = Error "cannot call impure function from pure context"
let error_cannot_access_mutable_captured_variable_from_pure_context name = Error (Printf.sprintf "cannot access mutable captured variable '%s' from pure context" name)
let error_not_a_compile_time_constant (name: string) = Error (Printf.sprintf "'%s' is not a compile-time constant" name)
let error_no_default_value = Error "no default value for this type"
let error_expected_const_lambda = Error "expected a const lambda"
let error_type_expected = Error "expected a type"