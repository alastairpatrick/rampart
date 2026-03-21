(* Constant expression aka compile-time constant expression aka CTCE: an expression that can be evaluated to a const value at compile time
   Constant value: a literal, a lambda expression, or a composite value (tuple, dynamic array, etc.) whose elements are all constant values.
   Constant type: a constant value that represents a type. Subset of the constant values.
   Representative value: a constant value of a particular type that stands in for that type; only its type is meaningful.

   Constant expression > constant value > constant type
                         constant_value > representative value
*)


open Ast
open Error

let next_closure_identity = ref 0

let distinct_closure_identity () =
  let identity = !next_closure_identity in
  next_closure_identity := identity + 1;
  identity


(* The danger is calling this could cause distinct lambdas to appear equal. It is useful in tests, where we don't want the identity of a lambda to be affected by previously run tests. *)
let dangerously_reset_distinct_closure_identity () =
  next_closure_identity := 0

(* Structural equality on type‑expressions, ignoring source locations.
   Returns

     * [true] when both [a] and [b] are *syntactic* constant‑type forms and
       they denote the same type (eg. the same tuple shape or the same
       function signature).

     * [false] when both are constant types but differ, or when either
       operand is not itself a constant‑type expression.

   The test does **not** perform any sub‑evaluation; an expression that
   would evaluate to a type (for example a call to a const function) is
   treated as “not a const type” here unless it already has the required
   syntactic form.
*)

let rec const_types_equal (a : expression) (b : expression) : bool =
  match a, b with
  | (_, Type (Function (a_callee, a_param_types, a_modifiers))), (_, Type (Function (b_callee, b_param_types, b_modifiers))) ->
    const_types_equal a_callee b_callee && List.for_all2 const_types_equal a_param_types b_param_types && a_modifiers = b_modifiers
  | (_, Type a_type), (_, Type b_type) -> a_type = b_type
  | (_, Tuple a_elements), (_, Tuple b_elements) ->
    (try
      List.for_all2 const_types_equal a_elements b_elements
    with Invalid_argument _ -> false)
  | (_, Index (a_type, None)), (_, Index (b_type, None)) -> (* TODO: for now, only dynamic arrays are supported. In the future, the size expression can be an int literal for fixed size arrays. *)
    const_types_equal a_type b_type
  | _ -> false

let is_const_type (expression : expression) : bool = const_types_equal expression expression

let check_is_const_type expression =
  if is_const_type expression then expression else raise error_type_expected

let rec const_values_equal (a : expression) (b : expression) : bool =
  match a, b with
  | (_, IntLiteral a), (_, IntLiteral b) -> a = b
  | (_, BoolLiteral a), (_, BoolLiteral b) -> a = b
  | (_, Tuple a_elements), (_, Tuple b_elements) ->
    (try
      List.for_all2 const_values_equal a_elements b_elements
    with Invalid_argument _ -> false)
  (* Invariant on dynamic arrays of constant value: all elements have the type designated by the element type field, which is never None. *)
  | (_, DynamicArray (a_elements, Some a_type)), (_, DynamicArray (b_elements, Some b_type)) ->
    (try
      Array.for_all2 const_values_equal a_elements b_elements && const_types_equal a_type b_type
    with Invalid_argument _ -> false)
  | (_, Lambda (_, _, _, _, Some (a_identity, _))), (_, Lambda (_, _, _, _, Some (b_identity, _))) ->
    a_identity == b_identity
  | _ when is_const_type a && is_const_type b -> const_types_equal a b
  | _ -> false

let rec is_const_value (expression : expression) : bool =
  match expression with
  | _, IntLiteral _ -> true
  | _, BoolLiteral _ -> true
  | _, Type _ -> true
  | _, Tuple elements -> List.for_all is_const_value elements
  | _, DynamicArray (elements, Some element_type) -> Array.for_all is_const_value elements && is_const_type element_type
  | _, Lambda _ -> true
  | _ when is_const_type expression -> true
  | _ -> false

let rec const_value_for_all (predicate : expression -> bool) expression : bool =
  match expression with
  | _, Tuple elements -> List.for_all (const_value_for_all predicate) elements
  | _, DynamicArray (elements, _) -> Array.for_all (const_value_for_all predicate) elements
  | _ -> predicate expression 

let const_value_exists (predicate : expression -> bool) expression : bool =
  not (const_value_for_all (fun e -> not (predicate e)) expression)

(* This must work on any const value, which by definition includes any lambda (const or not) and any representative value. *)
let rec type_of_expression ((location, expression): expression) : expression =
  match expression with
  | IntLiteral _ -> (location, Type Int)
  | BoolLiteral _ -> (location, Type Bool)
  | Type _ -> (location, Type Type)
  | Tuple elements -> (location, Tuple (List.map type_of_expression elements))
  | TypeOf _ -> (location, Type Type)
  | DynamicArray (_, Some element_type) -> (location, Index (element_type, None))
  | Lambda (return_type, params, modifiers, _, _) ->
    let param_types = List.map (fun (_, param) -> match param with
      | BoundDeclaration ({type_expr=Some type_expr; _}, _) -> type_expr
      | _ -> assert false) params in
    (location, Type (Function (return_type, param_types, modifiers)))
  | _ when is_const_type (location, expression) -> (location, Type Type)
  | _ -> print_endline (Printf.sprintf "expression not implemented: %s" (Ast.show_expression (location, expression))); assert false (* TODO: implement for more expressions as needed *)

let rec default_value ((location, const_type): expression) : expression =
  match const_type with
  | Type Int -> (location, IntLiteral 0)
  | Type Bool -> (location, BoolLiteral false)
  | Tuple elements ->
    (location, Tuple (List.map default_value elements))
  | Index (element_type, None) ->
    (location, DynamicArray ([| |], Some element_type))
  | _ -> raise error_no_default_value
  
let rec representative_value_of_type ((location, const_type): expression) : expression =
  let representative_value = match const_type with
    | Type Int -> (location, IntLiteral 0)
    | Type Bool -> (location, BoolLiteral false)
    | Type Type -> (location, Type Type)
    | Type (Function (return_type, param_types, modifiers)) ->
      (location, Lambda (return_type,
        List.map (fun param_type -> (location, BoundDeclaration ({type_expr=Some param_type; init_expr=None; name=""; modifiers=empty_declaration_modifiers}, {index=0; depth=0; mut=false}))) param_types,
        modifiers, (location, Compound []), None))
    | Tuple elements ->
      (location, Tuple (List.map representative_value_of_type elements))
    | Index (element_type, None) ->
      (location, DynamicArray ([| |], Some element_type))
    | _ -> raise (error_internal (Printf.sprintf "representative value not implemented for type expression: %s" (Ast.show_expression (location, const_type)))) 
  in
    if (not (is_const_value representative_value)) then
      raise (error_internal (Printf.sprintf "representative value should be a const value: %s" (Ast.show_expression representative_value)))
    else
      representative_value