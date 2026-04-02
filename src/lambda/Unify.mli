open Whnf_intf
include module type of Unify_intf

module MakeUnify (Unify__0 : sig
  (*! structure IntSyn' : INTSYN !*)
  module Whnf : WHNF

  (*! sharing Whnf.IntSyn = IntSyn' !*)
  module Trail : TRAIL
end) : UNIFY
