include module type of Mtp_filling_intf

module MTPFilling (MTPFilling__0 : sig
  module MTPGlobal : Mtp_global.MTPGLOBAL

  (*! structure IntSyn : INTSYN !*)
  (*! structure FunSyn' : FUNSYN !*)
  (*! sharing FunSyn'.IntSyn = IntSyn !*)
  module StateSyn' : Statesyn_intf.STATESYN

  (*! sharing StateSyn'.FunSyn = FunSyn' !*)
  module Abstract : ABSTRACT

  (*! sharing Abstract.IntSyn = IntSyn !*)
  module TypeCheck : TYPECHECK

  (*! sharing TypeCheck.IntSyn = IntSyn !*)
  module MTPData : Mtp_data_intf.MTPDATA
  module Search : Mtp_search_intf.MTPSEARCH
  module Whnf : WHNF
end) : Mtp_filling_intf.MTPFILLING
