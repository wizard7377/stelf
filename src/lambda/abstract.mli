include module type of Abstract_intf

module MakeAbstract (Abstract__0 : sig
  (*! structure IntSyn' : INTSYN !*)
  module Whnf : Whnf.WHNF

  (*! sharing Whnf.IntSyn = IntSyn' !*)
  module Unify : Unify.UNIFY

  (*! sharing Unify.IntSyn = IntSyn' !*)
  module Constraints : Constraints.CONSTRAINTS
end) : ABSTRACT
