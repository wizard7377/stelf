include module type of MTPMPI

module MTPi (MTPi__0 : sig
  module MTPGlobal : MtpGlobal.MTPGLOBAL

  (*! structure IntSyn : INTSYN !*)
  (*! structure FunSyn' : FUNSYN !*)
  (*! sharing FunSyn'.IntSyn = IntSyn !*)
  module StateSyn' : STATESYN.STATESYN

  (*! sharing StateSyn'.IntSyn = IntSyn !*)
  (*! sharing StateSyn'.FunSyn = FunSyn' !*)
  module RelFun : RELFUN.RELFUN

  (*! sharing RelFun.FunSyn = FunSyn' !*)
  module Formatter : FORMATTER
  module Print : PRINT

  (*! sharing Print.IntSyn = IntSyn !*)
  module FunTypeCheck : FUNTYPECHECK.FUNTYPECHECK

  (*! sharing FunTypeCheck.FunSyn = FunSyn' !*)
  module MTPData : MTPDATA.MTPDATA
  module MTPInit : MTPINIT.MTPINIT

  (*! sharing MTPInit.FunSyn = FunSyn' !*)
  module MTPFilling : MTPFILLING.MTPFILLING

  (*! sharing MTPFilling.FunSyn = FunSyn' !*)
  module Inference : INFERENCE.INFERENCE

  (*! sharing Inference.FunSyn = FunSyn' !*)
  module MTPSplitting : MTPSPLITTING.MTPSPLITTING
  module MTPRecursion : MTPRECURSION.MTPRECURSION
  module MTPStrategy : MTPSTRATEGY.MTPSTRATEGY
  module MTPrint : MTPPRINT.MTPRINT
  module Order : ORDER

  (*! sharing Order.IntSyn = IntSyn !*)
  module Names : NAMES

  (*! sharing Names.IntSyn = IntSyn !*)
  module Timers : TIMERS.TIMERS
  module Ring : RING.RING
end) : MTPI
