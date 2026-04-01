include module type of Mtp_recursion_intf

module MTPRecursion (MTPRecursion__0 : sig
  module MTPGlobal : Mtp_global.MTPGLOBAL
  module Global : GLOBAL

  (*! structure IntSyn : INTSYN !*)
  (*! structure FunSyn : FUNSYN !*)
  (*! sharing FunSyn.IntSyn = IntSyn !*)
  module StateSyn' : Statesyn_intf.STATESYN

  (*! sharing StateSyn'.IntSyn = IntSyn !*)
  (*! sharing StateSyn'.FunSyn = FunSyn !*)
  module Abstract : ABSTRACT

  (*! sharing Abstract.IntSyn = IntSyn !*)
  module MTPAbstract : Mtp_abstract_intf.MTPABSTRACT

  (*! sharing MTPAbstract.IntSyn = IntSyn !*)
  (*! sharing MTPAbstract.FunSyn = FunSyn !*)
  module FunTypeCheck : Funtypecheck_intf.FUNTYPECHECK

  (*! sharing FunTypeCheck.FunSyn = FunSyn !*)
  module MTPrint : Mtp_print_intf.MTPRINT
  module Whnf : WHNF

  (*! sharing Whnf.IntSyn = IntSyn !*)
  module Unify : UNIFY

  (*! sharing Unify.IntSyn = IntSyn !*)
  module Conv : CONV

  (*! sharing Conv.IntSyn = IntSyn !*)
  module Names : NAMES

  (*! sharing Names.IntSyn = IntSyn !*)
  module Subordinate : Subordinate_.SUBORDINATE

  (*! sharing Subordinate.IntSyn = IntSyn !*)
  module Print : PRINT

  (*! sharing Print.IntSyn = IntSyn !*)
  module TypeCheck : TYPECHECK

  (*! sharing TypeCheck.IntSyn = IntSyn !*)
  module Formatter : FORMATTER
  module FunPrint : Funprint_intf.FUNPRINT
end) : MTPRECURSION
