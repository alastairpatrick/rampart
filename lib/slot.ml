open Sexplib
open Sexplib.Std

type slot = { index: int; depth: int  }

type display_slot = int * int
[@@deriving sexp, show]

let sexp_of_slot { index; depth } : Sexp.t = sexp_of_display_slot (index, depth)
let slot_of_sexp sexp : slot = let (index, depth) = display_slot_of_sexp sexp in { index; depth }
let show_slot { index; depth } : string = show_display_slot (index, depth)
let pp_slot fmt { index; depth } = pp_display_slot fmt (index, depth)
