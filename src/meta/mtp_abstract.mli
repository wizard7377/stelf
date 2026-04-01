include module type of Mtp_abstract_intf

module MTPAbstract (MTPAbstract__0 : sig
  (*! structure IntSyn' : INTSYN !*)
  (*! structure FunSyn' : FUNSYN !*)
  (*! sharing FunSyn'.IntSyn = IntSyn' !*)
  module StateSyn' : Statesyn_intf.STATESYN

  (*! sharing StateSyn'.FunSyn = FunSyn' !*)
  module Whnf : WHNF

  (*! sharing Whnf.IntSyn = IntSyn' !*)
  module Constraints : CONSTRAINTS

  (*! sharing Constraints.IntSyn = IntSyn' !*)
  module Unify : UNIFY

  (*! sharing Unify.IntSyn = IntSyn' !*)
  module Subordinate : Subordinate_.SUBORDINATE

  (*! sharing Subordinate.IntSyn = IntSyn' !*)
  module TypeCheck : TYPECHECK

  (*! sharing TypeCheck.IntSyn = IntSyn' !*)
  module FunTypeCheck : Funtypecheck_intf.FUNTYPECHECK

  (*! sharing FunTypeCheck.FunSyn = FunSyn' !*)
  module Abstract : ABSTRACT
end) : Mtp_abstract_intf.MTPABSTRACT
