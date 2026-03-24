(* Constant expression aka compile-time constant expression aka CTCE: an expression that can be evaluated to a const value at compile time
   Constant value: a literal, a lambda expression, or a composite value (tuple, dynamic array, etc.) whose elements are all constant values.
   Constant type: a constant value that represents a type. Subset of the constant values.
   Representative value: a constant value of a particular type that stands in for that type; only its type is meaningful.

   Constant expression > constant value > constant type
                         constant_value > representative value
*)


open Ast
open Error
open Location

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

let check_is_const_type expression : const_type_expression =
  match expression with
  | _, Type t -> t
  | _ -> raise error_type_expected

let rec const_values_equal (a : expression) (b : expression) : bool =
  match a, b with
  | (_, Int_literal a), (_, Int_literal b) -> a = b
  | (_, Bool_literal a), (_, Bool_literal b) -> a = b
  | (_, Tuple a_elements), (_, Tuple b_elements) ->
    (try
      List.for_all2 const_values_equal a_elements b_elements
    with Invalid_argument _ -> false)
  (* Invariant on dynamic arrays of constant value: all elements have the type designated by the element type field, which is never None. *)
  | (_, Dynamic_array (a_elements, a_type)), (_, Dynamic_array (b_elements, b_type)) ->
    (try
      Array.for_all2 const_values_equal a_elements b_elements && a_type = b_type
    with Invalid_argument _ -> false)
  | (_, Lambda (_, _, _, _, Some (a_identity, _))), (_, Lambda (_, _, _, _, Some (b_identity, _))) ->
    a_identity = b_identity
  | _ -> a = b

let rec is_const_value (expression : expression) : bool =
  match expression with
  | _, Int_literal _ -> true
  | _, Bool_literal _ -> true
  | _, Type _ -> true
  | _, Tuple elements -> List.for_all is_const_value elements
  | _, Dynamic_array (elements, _) -> Array.for_all is_const_value elements
  | _, Lambda _ -> true
  | _ -> false

let rec const_value_for_all (predicate : expression -> bool) expression : bool =
  match expression with
  | _, Tuple elements -> List.for_all (const_value_for_all predicate) elements
  | _, Dynamic_array (elements, _) -> Array.for_all (const_value_for_all predicate) elements
  | _ -> predicate expression 

let const_value_exists (predicate : expression -> bool) expression : bool =
  not (const_value_for_all (fun e -> not (predicate e)) expression)

(* This must work on any const value, which by definition includes any lambda (const or not) and any representative value. *)
let rec type_of_expression ((location, expression): expression) : const_type_expression =
  match expression with
  | Int_literal _ -> Int
  | Bool_literal _ -> Bool
  | Type _ -> Type
  | Tuple elements -> Tuple (List.map type_of_expression elements)
  | Type_of _ -> Type
  | Dynamic_array (_, element_type) -> Dynamic_array element_type
  | Lambda (return_type, params, modifiers, _, _) ->
    let param_types = List.map (fun (_, param) -> match param with
      | Bound_declaration ({typ=param_type; _}, _) -> param_type
      | _ -> assert false) params in
    Function (return_type, param_types, modifiers)
  | _ -> print_endline (Printf.sprintf "expression not implemented: %s" (Ast.show_expression (location, expression))); assert false (* TODO: implement for more expressions as needed *)

let rec default_value const_type : expression =
  match const_type with
  | Int -> (null_location, Int_literal 0L)
  | Bool -> (null_location, Bool_literal false)
  | (Tuple elements) ->
    (null_location, Tuple (List.map (fun element -> default_value element) elements))
  | (Dynamic_array element_type) ->
    (null_location, Dynamic_array ([| |], element_type))
  | _ -> raise error_no_default_value
  
let rec representative_value_of_type (const_type: const_type_expression) : expression =
  let representative_value = match const_type with
    | Int -> (null_location, Int_literal 0L)
    | Bool -> (null_location, Bool_literal false)
    | Type -> (null_location, Type Representative)
    | Function (return_type, param_types, modifiers) ->
      (null_location, Lambda (return_type,
        List.map (fun param_type -> (null_location, Bound_declaration ({typ=param_type; init_expr=None; name=""; modifiers=empty_declaration_modifiers}, {index=0; depth=0; mut=false}))) param_types,
        modifiers, (null_location, Compound []), None))
    | Tuple elements ->
      (null_location, Tuple (List.map (fun element -> representative_value_of_type element) elements))
    | Dynamic_array element_type ->
      (null_location, Dynamic_array ([| |], element_type))
    | _ -> raise (error_internal (Printf.sprintf "representative value not implemented for type expression: %s" (Ast.show_const_type_expression const_type))) 
  in
    if (not (is_const_value representative_value)) then
      raise (error_internal (Printf.sprintf "representative value should be a const value: %s" (Ast.show_expression representative_value)))
    else
      representative_value