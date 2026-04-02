include module type of MtpFilling_intf

module MTPFilling (MTPFilling__0 : sig
  module MTPGlobal : MtpGlobal.MTPGLOBAL

  (*! structure IntSyn : INTSYN !*)
  (*! structure FunSyn' : FUNSYN !*)
  (*! sharing FunSyn'.IntSyn = IntSyn !*)
  module StateSyn' : Statesyn_intf.STATESYN

  (*! sharing StateSyn'.FunSyn = FunSyn' !*)
  module Abstract : ABSTRACT

  (*! sharing Abstract.IntSyn = IntSyn !*)
  module TypeCheck : TYPECHECK

  (*! sharing TypeCheck.IntSyn = IntSyn !*)
  module MTPData : MtpData_intf.MTPDATA
  module Search : MtpSearch_intf.MTPSEARCH
  module Whnf : WHNF
end) : MtpFilling_intf.MTPFILLING
