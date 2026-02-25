open Error
open Type

type implementation_value = ..

type assignable = (* array_idx: *) int * value array

(* Tuples are represented as mutable arrays, except for singletons, which have an explicit representation. This
is primarily for performance reasons; we want to avoid heap allocations for singletons. Use tuple_value to convert
from array of values to value; it normalizes appropriately. *)
and value =
  | Uninitialized of typ option
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
  | Uninitialized None -> Uninitialized
  | Uninitialized (Some typ) -> typ
  | Failed -> raise Saw_failed_error
  | Assignable ((idx, arr), _) -> type_of_value arr.(idx)
  | Int _ -> Singleton Int
  | Bool _ -> Singleton Bool
  | SingletonType _ -> Singleton Type
  | Tuple [| _ |] -> assert false (* Assert becaused this is a logic error; singletons have an explicit representation *)
  | Tuple elements -> tuple_type (Array.to_list (Array.map type_of_value elements))
  | Impl (typ, _) -> typ

let rec show_value (v: value) : string = match v with
  | Uninitialized _ -> "[:uninitialized:]"
  | Failed -> "[:failed:]"
  | Assignable ((idx, arr), name) -> Printf.sprintf "'%s'=%s" name (show_value arr.(idx))
  | Int v -> string_of_int v
  | Bool v -> string_of_bool v
  | SingletonType t -> show_type (Singleton t)
  | Tuple [| |] -> "void"
  | Tuple [| _ |] -> assert false (* Assert becaused this is a logic error; singletons have an explicit representation *)
  | Tuple elements -> Printf.sprintf "(%s)" (String.concat "," (List.map show_value (Array.to_list elements)))
  | Impl (typ, _) -> Printf.sprintf "[:impl %s:]" (show_type typ)


let rec value_to_type (value : value) : typ = match value with
  | SingletonType typ -> Singleton typ
  | Tuple [| _ |] -> assert false
  | Tuple elements -> tuple_type (Array.to_list (Array.map value_to_type elements))
  | _ -> raise error_not_a_type

let rec type_to_value (typ : typ) : value = match typ with
  | Uninitialized -> assert false
  | Singleton typ -> SingletonType typ
  | Tuple types -> Tuple (Array.of_list (List.map type_to_value types))

let rec is_value_complete (value : value) : bool = match value with
  | Uninitialized _ -> false
  | Failed -> false
  | Assignable ((idx, arr), _) -> is_value_complete arr.(idx)
  | _ -> true

let rec is_value_type (value : value) : bool = match value with
  | SingletonType _ -> true
  | Tuple [| _ |] -> assert false
  | Tuple elements -> Array.for_all is_value_type elements
  | _ -> false

let rec default_value (typ: typ) : value =
  match typ with
  | Singleton Int -> Int 0
  | Singleton Bool -> Bool false
  | Tuple [] -> void
  | Tuple types -> Tuple (Array.of_list (List.map default_value types))
  | _ -> raise (Error (Printf.sprintf "type '%s' does not have a default value" (show_type typ)))
