(* This language makes no distinction between a type and a 1-tuple of that type; they are the same type. *)
type singleton_type =
  | Int
  | Bool
  | Type
  | Function of typ * typ Iarray.t * (* pure: *) bool

and typ =
  | Singleton of singleton_type
  | Tuple of typ Iarray.t       (* Must never contain a single element; use Singleton instead; tuple_type can be used to normalize *)

let void_type = Tuple [| |]

let tuple_type (types : typ Seq.t) =
  match Seq.uncons types with
  | None -> void_type
  | Some (h, t) -> match Seq.uncons t with
    | None -> h
    | Some _ -> Tuple (Iarray.of_seq (Seq.cons h t))

let rec show_typ (t: typ) : string = match t with
  | Singleton Int -> "int"
  | Singleton Bool -> "bool"
  | Singleton Type -> "type"
  | Singleton Function (return_type, param_types, pure) -> Printf.sprintf "%s%s(%s)" (show_typ return_type) (if pure then " pure" else "") (String.concat "," (List.map show_typ (Iarray.to_list param_types)))
  | Tuple [| |] -> "void"
  | Tuple [| _ |] -> assert false
  | Tuple ts -> Printf.sprintf "(%s)" (String.concat ", " (Seq.map show_typ (Iarray.to_seq ts) |> List.of_seq))
