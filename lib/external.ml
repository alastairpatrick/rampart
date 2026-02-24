(*
let external_function (return_type : typ) (param_types : typ list) (f : (value list -> value)) : expression =
  (null_location, External (Value (Impl (Singleton (Function (return_type, param_types)), ExternalFunction f))))

let external_declaration (return_type : typ) (param_types : typ list) (name : string) (f : (value list -> value)) : statement =
  (null_location, Declaration {type_expr=None; name=name; init_expr=Some (external_function return_type param_types f)})

let print (args : value list) : value =
  List.iter (fun v -> print_endline (show_value v)) args;
  Void

let wrap_external (statements : statement list) : statement list = [
  external_declaration Void [Singleton Int] "print" print;
  (null_location, (OrderIndependent statements));
]
*)