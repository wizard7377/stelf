include module type of AbstractTabled_intf

module AbstractTabled (AbstractTabled__0 : sig
  (*! structure IntSyn' : INTSYN !*)
  module Whnf : WHNF

  (*! sharing Whnf.IntSyn = IntSyn' !*)
  module Unify : UNIFY

  (*! sharing Unify.IntSyn = IntSyn' !*)
  module Constraints : CONSTRAINTS

  (*! sharing Constraints.IntSyn = IntSyn' !*)
  module Subordinate : Subordinate.Subordinate_.SUBORDINATE

  (*! sharing Subordinate.IntSyn = IntSyn' !*)
  module Print : PRINT

  (*! sharing Print.IntSyn = IntSyn' !*)
  module Conv : CONV
end) : ABSTRACTTABLED
