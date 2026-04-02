include module type of Statesyn_intf

module StateSyn (StateSyn__0 : sig
  (*! structure IntSyn' : INTSYN !*)
  (*! structure FunSyn' : FUNSYN !*)
  (*! sharing FunSyn'.IntSyn = IntSyn' !*)
  module Whnf : WHNF

  (*! sharing Whnf.IntSyn = IntSyn' !*)
  module Conv : CONV
end) : Statesyn_intf.STATESYN
