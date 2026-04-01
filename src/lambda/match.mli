open Whnf_intf
open Unify_intf
include module type of Match_intf

module MakeMatch (Match__0 : sig
  (*! structure IntSyn' : INTSYN !*)
  module Whnf : WHNF

  (*! sharing Whnf.IntSyn = IntSyn' !*)
  module Unify : UNIFY
  module Trail : TRAIL
end) : MATCH
