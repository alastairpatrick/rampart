type slot = { index: int; depth: int; mut: bool  }

type display_slot = int * int
[@@deriving show]

let show_slot { index; depth; _ } : string = show_display_slot (index, depth)
let pp_slot fmt { index; depth; _ } = pp_display_slot fmt (index, depth)

let unbindable_slot = { index=(-1); depth=(-1); mut=false }
let is_slot_bindable slot = slot.index >= 0