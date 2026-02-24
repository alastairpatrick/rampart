open Sexplib.Std

type singleton_type =
  | Int
  | Bool
  | Type
  | Function of typ * typ list

and typ =
  | Uninitialized
  | Singleton of singleton_type
  | Tuple of typ list
[@@deriving sexp, show]

let tuple_type types =
  match types with
  | [singleton] -> singleton
  | _ -> Tuple types

let rec show_type (t: typ) : string = match t with
  | Uninitialized -> ":uninitialized:"
  | Singleton Int -> "int"
  | Singleton Bool -> "bool"
  | Singleton Type -> "type"
  | Singleton Function (return_type, param_types) -> Printf.sprintf "%s(%s)" (show_type return_type) (String.concat "," (List.map show_type param_types))
  | Tuple [] -> "void"
  | Tuple [_] -> assert false
  | Tuple ts -> Printf.sprintf "(%s)" (String.concat ", " (List.map show_type ts))
