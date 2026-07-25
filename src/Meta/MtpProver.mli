include module type of MTPPROVER

module MTProver (MTProver__0 : sig
  module MTPGlobal : MtpGlobal.MTPGLOBAL

  (*! structure IntSyn' : INTSYN !*)
  (*! structure FunSyn : FUNSYN !*)
  (*! sharing FunSyn.IntSyn = IntSyn' !*)
  module StateSyn : STATESYN.STATESYN

  (*! sharing IntSyn = IntSyn' !*)
  (*! sharing StateSyn.FunSyn = FunSyn !*)
  module Order : ORDER

  (*! sharing Order.IntSyn = IntSyn' !*)
  module MTPInit : MTPINIT.MTPINIT

  (*! sharing MTPInit.FunSyn = FunSyn !*)
  module MTPStrategy : MTPSTRATEGY.MTPSTRATEGY
  module RelFun : RELFUN.RELFUN
end) : MTPPROVER.MTPROVER

module CombiProver (CombiProver__1 : sig
  module MTPGlobal : MtpGlobal.MTPGLOBAL

  (*! structure IntSyn' : INTSYN !*)
  module ProverOld : Prover.PROVER

  (*! sharing ProverOld.IntSyn = IntSyn' !*)
  module ProverNew : MTPPROVER.MTPROVER
end) : MTPPROVER.MTPROVER
