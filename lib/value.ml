open Error
open Type

type implementation_value = ..

type variable_modifiers = {
  mut: bool;
}

type variable = {
  value: value;
  modifiers: variable_modifiers
}

and assignable = (* array_idx: *) int * variable array

(* Tuples are represented as mutable arrays, except for singletons, which have an explicit representation. This
is primarily for performance reasons; we want to avoid heap allocations for singletons. Use tuple_value to convert
from array of values to value; it normalizes appropriately. *)
and value =
  | Uninitialized of typ option
  | Failed
  | Assignable of assignable * (*display_name: *) string
  | Int of int
  | Bool of bool
  | Type of typ
  | Tuple of value array
  | Impl of typ * implementation_value

let tuple_value (values : value Seq.t) =
  match Seq.uncons values with
  | None -> Tuple [||]
  | Some (value, rest) -> match Seq.uncons rest with
    | None -> value
    | Some _ -> Tuple (Array.of_seq (Seq.cons value rest))

let void = Tuple [| |]

let empty_variable = { value = Uninitialized None; modifiers = { mut = false } }

let rec type_of_value (value: value) : typ =
  match value with
  | Uninitialized None -> assert false
  | Uninitialized (Some typ) -> typ
  | Failed -> raise Saw_failed_error
  | Assignable ((idx, arr), _) -> type_of_value arr.(idx).value
  | Int _ -> Singleton Int
  | Bool _ -> Singleton Bool
  | Type _ -> Singleton Type
  | Tuple [| _ |] -> assert false (* Assert becaused this is a logic error; singletons have an explicit representation *)
  | Tuple elements -> tuple_type (Seq.map type_of_value (Array.to_seq elements))
  | Impl (typ, _) -> typ

let rec show_value (v: value) : string = match v with
  | Uninitialized _ -> "[:uninitialized:]"
  | Failed -> "[:failed:]"
  | Assignable ((idx, arr), name) -> Printf.sprintf "'%s'=%s" name (show_value arr.(idx).value)
  | Int v -> string_of_int v
  | Bool v -> string_of_bool v
  | Type t -> show_typ t
  | Tuple [| |] -> "void"
  | Tuple [| _ |] -> assert false (* Assert becaused this is a logic error; singletons have an explicit representation *)
  | Tuple elements -> Printf.sprintf "(%s)" (String.concat "," (List.map show_value (Array.to_list elements)))
  | Impl (typ, _) -> Printf.sprintf "[:impl %s:]" (show_typ typ)

let rec value_to_type (value : value) : typ = match value with
  | Type typ -> typ
  | Tuple [| _ |] -> assert false (* logic error *)
  | Tuple elements -> (*tuple_type (Array.to_seq (Array.map value_to_type elements))*)
    tuple_type (Seq.map value_to_type (Array.to_seq elements))
  | _ -> raise error_not_a_type

let type_to_value (typ : typ) : value = Type typ

let rec is_value_complete (value : value) : bool = match value with
  | Uninitialized _ -> false
  | Failed -> false
  | Assignable ((idx, arr), _) -> is_value_complete arr.(idx).value
  | _ -> true

let rec is_value_type (value : value) : bool = match value with
  | Type _ -> true
  | Tuple [| _ |] -> assert false
  | Tuple elements -> Array.for_all is_value_type elements
  | _ -> false

let rec default_value (typ: typ) : value =
  match typ with
  | Singleton Int -> Int 0
  | Singleton Bool -> Bool false
  | Tuple [| |] -> void
  | Tuple types -> tuple_value (Seq.map default_value (Iarray.to_seq types))
  | _ -> raise (Error (Printf.sprintf "type '%s' does not have a default value" (show_typ typ)))
