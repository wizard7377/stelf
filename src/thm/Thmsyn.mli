include module type of Thmsyn_intf

module ThmSyn (ThmSyn__0 : sig
  (*! structure IntSyn : INTSYN !*)
  (*! structure ModeSyn' : MODESYN !*)
  (*! sharing ModeSyn'.IntSyn = IntSyn !*)
  module Abstract : ABSTRACT

  (*! sharing Abstract.IntSyn = IntSyn !*)
  module Whnf : WHNF

  (*! sharing Whnf.IntSyn = IntSyn !*)
  (*! structure Paths' : PATHS !*)
  module Names' : NAMES
end) : THMSYN with module Names = ThmSyn__0.Names'
