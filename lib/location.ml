open Sexplib

type location = Lexing.position * Lexing.position

let show_location ((s, _): location) : string = Printf.sprintf "@%d" s.pos_lnum
let pp_location (_: Format.formatter) (_: location) : unit = ()

let sexp_of_location (l: location) : Sexp.t = Sexp.Atom (show_location l)

let make_location (start: Lexing.position) (curr: Lexing.position) = (start, curr)

let null_position: Lexing.position = { pos_fname=""; pos_lnum=0; pos_cnum=0; pos_bol=0 }

let null_location : location = (null_position, null_position)

let location_of_sexp (_: Sexp.t) : location = null_location

let filename_of_location ((a, _) : location) : string = a.pos_fname
let line_of_location ((a, _) : location) : int = a.pos_lnum
let chars_of_location ((a, b) : location) : int*int = (a.pos_cnum - a.pos_bol), (b.pos_cnum - a.pos_bol)

let string_of_location loc =
  let filename = filename_of_location loc in
  let n = line_of_location loc in
  let c1, c2 = chars_of_location loc in
  (if String.length filename != 0 then (Printf.sprintf "file '%s', " filename) else "") ^
  (Printf.sprintf "line %d, " n) ^
  (if c1+1 == c2 then (Printf.sprintf "character %d" (c1+1)) else (Printf.sprintf "characters %d-%d" (c1+1) c2))
