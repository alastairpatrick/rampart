open Sexplib
open Sexplib.Std

type slot = { index: int; depth: int; mut: bool  }

type display_slot = int * int
[@@deriving sexp, show]

(* We don't round trip between slot and sexp so it doesn't matter that display_slot drops mutability.*)
let sexp_of_slot { index; depth; _ } : Sexp.t = sexp_of_display_slot (index, depth)
let slot_of_sexp sexp : slot = let (index, depth) = display_slot_of_sexp sexp in { index; depth; mut = false }
let show_slot { index; depth; _ } : string = show_display_slot (index, depth)
let pp_slot fmt { index; depth; _ } = pp_display_slot fmt (index, depth)

let unbindable_slot = { index=(-1); depth=(-1); mut=false }
let is_slot_bindable slot = slot.index >= 0
