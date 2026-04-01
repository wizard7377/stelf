include module type of Funsyn_intf

module Make_FunSyn (FunSyn__0 : sig
  (*! structure IntSyn' : INTSYN !*)
  module Whnf : WHNF

  (*! sharing Whnf.IntSyn = IntSyn' !*)
  module Conv : CONV
end) : FUNSYN

module FunSyn : FUNSYN
