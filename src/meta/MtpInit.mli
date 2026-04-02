include module type of MtpInit_intf

module MTPInit (MTPInit__0 : sig
  module MTPGlobal : MtpGlobal.MTPGLOBAL
  module MTPData : MtpData_intf.MTPDATA

  (*! structure IntSyn : INTSYN !*)
  module Names : NAMES

  (*! sharing Names.IntSyn = IntSyn !*)
  (*! structure FunSyn' : FUNSYN !*)
  (*! sharing FunSyn'.IntSyn = IntSyn !*)
  module StateSyn' : Statesyn_intf.STATESYN

  (*! sharing StateSyn'.FunSyn = FunSyn' !*)
  module Formatter : FORMATTER
  module Whnf : WHNF

  (*! sharing Whnf.IntSyn = IntSyn !*)
  module Print : PRINT

  (*! sharing Print.IntSyn = IntSyn !*)
  module FunPrint : Funprint_intf.FUNPRINT
end) : MtpInit_intf.MTPINIT
