open Sexplib.Std

(* This language makes no distinction between a type and a 1-tuple of that type; they are the same type. *)
type singleton_type =
  | Int
  | Bool
  | Type
  | Function of typ * typ list

and typ =
  | Uninitialized
  | Singleton of singleton_type
  | Tuple of typ list       (* Must never contain a single element; use Singleton instead; tuple_type can be used to normalize *)
[@@deriving sexp, show]

let tuple_type (types : typ Seq.t) =
  match Seq.uncons types with
  | None -> Tuple []
  | Some (h, t) -> match Seq.uncons t with
    | None -> h
    | Some _ -> Tuple (h :: List.of_seq t)

let rec show_type (t: typ) : string = match t with
  | Uninitialized -> ":uninitialized:"
  | Singleton Int -> "int"
  | Singleton Bool -> "bool"
  | Singleton Type -> "type"
  | Singleton Function (return_type, param_types) -> Printf.sprintf "%s(%s)" (show_type return_type) (String.concat "," (List.map show_type param_types))
  | Tuple [] -> "void"
  | Tuple [_] -> assert false
  | Tuple ts -> Printf.sprintf "(%s)" (String.concat ", " (List.map show_type ts))
