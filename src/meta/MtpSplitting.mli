include module type of MtpSplitting_intf

module MTPSplitting (MTPSplitting__0 : sig
  module MTPGlobal : MtpGlobal.MTPGLOBAL
  module Global : GLOBAL

  (*! structure IntSyn : INTSYN !*)
  (*! structure FunSyn : FUNSYN !*)
  (*! sharing FunSyn.IntSyn = IntSyn !*)
  module StateSyn' : Statesyn_intf.STATESYN

  (*! sharing StateSyn'.FunSyn = FunSyn !*)
  (*! sharing StateSyn'.IntSyn = IntSyn !*)
  module Heuristic : HEURISTIC
  module MTPAbstract : MtpAbstract_intf.MTPABSTRACT

  (*! sharing MTPAbstract.IntSyn = IntSyn !*)
  module MTPrint : MtpPrint_intf.MTPRINT
  module Names : NAMES

  (* too be removed  -cs *)
  (*! sharing Names.IntSyn = IntSyn !*)
  (* too be removed  -cs *)
  module Conv : CONV

  (*! sharing Conv.IntSyn = IntSyn !*)
  module Whnf : WHNF

  (*! sharing Whnf.IntSyn = IntSyn !*)
  module TypeCheck : TYPECHECK

  (*! sharing TypeCheck.IntSyn = IntSyn !*)
  module Subordinate : Subordinate_.SUBORDINATE

  (*! sharing Subordinate.IntSyn = IntSyn !*)
  module FunTypeCheck : Funtypecheck_intf.FUNTYPECHECK

  (*! sharing FunTypeCheck.FunSyn = FunSyn !*)
  module Index : INDEX

  (*! sharing Index.IntSyn = IntSyn !*)
  module Print : PRINT

  (*! sharing Print.IntSyn = IntSyn !*)
  module Unify : UNIFY
end) : MtpSplitting_intf.MTPSPLITTING
