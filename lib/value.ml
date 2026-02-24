open Error
open Type

type implementation_value = ..

type assignable = (* array_idx: *) int * value array

and value =
  | Uninitialized
  | Failed
  | Assignable of assignable * (*display_name: *) string
  | Int of int
  | Bool of bool
  | SingletonType of singleton_type
  | Tuple of value array
  | Impl of typ * implementation_value

let tuple_value values =
  match values with
  | [| value |] -> value
  | _ -> Tuple values

let void = Tuple [| |]

let rec type_of_value (value: value) : typ =
  match value with
  | Uninitialized
  | Failed -> assert false
  | Assignable ((idx, arr), _) -> type_of_value arr.(idx)
  | Int _ -> Singleton Int
  | Bool _ -> Singleton Bool
  | SingletonType _ -> Singleton Type
  | Tuple [| _ |] -> assert false
  | Tuple elements -> tuple_type (Array.to_list (Array.map type_of_value elements))
  | Impl (typ, _) -> typ

let rec show_value (v: value) : string = match v with
  | Uninitialized -> "[:uninitialized:]"
  | Failed -> "[:failed:]"
  | Assignable ((idx, arr), name) -> Printf.sprintf "'%s'=%s" name (show_value arr.(idx))
  | Int v -> string_of_int v
  | Bool v -> string_of_bool v
  | SingletonType t -> show_type (Singleton t)
  | Tuple [| |] -> "void"
  | Tuple [| _ |] -> assert false
  | Tuple elements -> Printf.sprintf "(%s)" (String.concat "," (List.map show_value (Array.to_list elements)))
  | Impl (typ, _) -> Printf.sprintf "[:impl %s:]" (show_type typ)


let rec value_to_type (value : value) : typ = match value with
  | SingletonType typ -> Singleton typ
  | Tuple [| _ |] -> assert false
  | Tuple elements -> tuple_type (Array.to_list (Array.map value_to_type elements))
  | _ -> raise error_not_a_type

let rec is_value_uninitialized (value : value) : bool = match value with
  | Uninitialized -> true
  | Failed -> true
  | Assignable ((idx, arr), _) -> is_value_uninitialized arr.(idx)
  | _ -> false

let rec is_value_type (value : value) : bool = match value with
  | SingletonType _ -> true
  | Tuple [| _ |] -> assert false
  | Tuple elements -> Array.fold_left (fun acc element -> acc && is_value_type element) true elements
  | _ -> false

let default_value (typ: typ) : value =
  match typ with
  | Singleton Int -> Int 0
  | Singleton Bool -> Bool false
  | _ -> raise (Error (Printf.sprintf "type '%s' does not have a default value" (show_type typ)))
