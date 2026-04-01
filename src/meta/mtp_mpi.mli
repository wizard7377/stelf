include module type of Mtp_mpi_intf

module MTPi (MTPi__0 : sig
  module MTPGlobal : Mtp_global.MTPGLOBAL

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
  module MTPData : Mtp_data_intf.MTPDATA
  module MTPInit : Mtp_init_intf.MTPINIT

  (*! sharing MTPInit.FunSyn = FunSyn' !*)
  module MTPFilling : Mtp_filling_intf.MTPFILLING

  (*! sharing MTPFilling.FunSyn = FunSyn' !*)
  module Inference : Inference_intf.INFERENCE

  (*! sharing Inference.FunSyn = FunSyn' !*)
  module MTPSplitting : Mtp_splitting_intf.MTPSPLITTING
  module MTPRecursion : Mtp_recursion_intf.MTPRECURSION
  module MTPStrategy : Mtp_strategy_intf.MTPSTRATEGY
  module MTPrint : Mtp_print_intf.MTPRINT
  module Order : ORDER

  (*! sharing Order.IntSyn = IntSyn !*)
  module Names : NAMES

  (*! sharing Names.IntSyn = IntSyn !*)
  module Timers : Timers_intf.TIMERS
  module Ring : Ring_intf.RING
end) : MTPI
