include module type of MtpMpi_intf

module MTPi (MTPi__0 : sig
  module MTPGlobal : MtpGlobal.MTPGLOBAL

  (*! structure IntSyn : INTSYN !*)
  (*! structure FunSyn' : FUNSYN !*)
  (*! sharing FunSyn'.IntSyn = IntSyn !*)
  module StateSyn' : Statesyn_intf.STATESYN

  (*! sharing StateSyn'.IntSyn = IntSyn !*)
  (*! sharing StateSyn'.FunSyn = FunSyn' !*)
  module RelFun : Relfun_intf.RELFUN

  (*! sharing RelFun.FunSyn = FunSyn' !*)
  module Formatter : FORMATTER
  module Print : PRINT

  (*! sharing Print.IntSyn = IntSyn !*)
  module FunTypeCheck : Funtypecheck_intf.FUNTYPECHECK

  (*! sharing FunTypeCheck.FunSyn = FunSyn' !*)
  module MTPData : MtpData_intf.MTPDATA
  module MTPInit : MtpInit_intf.MTPINIT

  (*! sharing MTPInit.FunSyn = FunSyn' !*)
  module MTPFilling : MtpFilling_intf.MTPFILLING

  (*! sharing MTPFilling.FunSyn = FunSyn' !*)
  module Inference : Inference_intf.INFERENCE

  (*! sharing Inference.FunSyn = FunSyn' !*)
  module MTPSplitting : MtpSplitting_intf.MTPSPLITTING
  module MTPRecursion : MtpRecursion_intf.MTPRECURSION
  module MTPStrategy : MtpStrategy_intf.MTPSTRATEGY
  module MTPrint : MtpPrint_intf.MTPRINT
  module Order : ORDER

  (*! sharing Order.IntSyn = IntSyn !*)
  module Names : NAMES

  (*! sharing Names.IntSyn = IntSyn !*)
  module Timers : Timers_intf.TIMERS
  module Ring : Ring_intf.RING
end) : MTPI
