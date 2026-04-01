include module type of Mtp_init_intf

module MTPInit (MTPInit__0 : sig
  module MTPGlobal : Mtp_global.MTPGLOBAL
  module MTPData : Mtp_data_intf.MTPDATA

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
end) : Mtp_init_intf.MTPINIT
