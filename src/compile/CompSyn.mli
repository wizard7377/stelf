include module type of CompSyn_intf

module Make_CompSyn (CompSyn__0 : sig
  module Global : GLOBAL

  (*! structure IntSyn' : INTSYN !*)
  module Names : NAMES

  (*! sharing Names.IntSyn = IntSyn' !*)
  module Table : TABLE with type key = int
end) : COMPSYN

module CompSyn : COMPSYN

include COMPSYN
