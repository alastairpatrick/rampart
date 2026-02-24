open Ast
open Location

let prelower_if (location : location) (c : expression) (a : statement) (b : statement option) : statement =
  match b with
  | Some b -> location, (If (c, a, b))
  | None -> location, (If (c, a, (location, Compound [])))

let prelower_for location (init : statement) (cond : expression) (next : expression) (body : statement) : statement =
  location, Compound [
    init;
    location, If (cond,
      (location, DoWhile ((location, Compound [body; (location, Expression next)]), cond)
      ), (null_location, Compound []));
  ]

let prelower_while (location : location) (cond : expression) (body : statement) : statement =
  location, If (cond,
    (location, DoWhile (body, cond)
    ), (null_location, Compound []))
(*
let prelower_assignment (location : location) (a : expression) (b : expression) : expression =
  let rec flatten expr : (expression * int list) list =
    match expr with
    | _, Tuple elements -> List.mapi (fun i e -> List.map (fun (subexpr, indices) -> (subexpr, i::indices)) (flatten e)) elements |> List.flatten
    | _ -> [expr, []] in
  location, Decomposition (flatten a, b)
*)