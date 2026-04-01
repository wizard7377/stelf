include module type of Mtp_prover_intf

module MTProver (MTProver__0 : sig
  module MTPGlobal : Mtp_global.MTPGLOBAL

  (*! structure IntSyn' : INTSYN !*)
  (*! structure FunSyn : FUNSYN !*)
  (*! sharing FunSyn.IntSyn = IntSyn' !*)
  module StateSyn : Statesyn_intf.STATESYN

  (*! sharing IntSyn = IntSyn' !*)
  (*! sharing StateSyn.FunSyn = FunSyn !*)
  module Order : ORDER

  (*! sharing Order.IntSyn = IntSyn' !*)
  module MTPInit : Mtp_init_intf.MTPINIT

  (*! sharing MTPInit.FunSyn = FunSyn !*)
  module MTPStrategy : Mtp_strategy_intf.MTPSTRATEGY
  module RelFun : Relfun_intf.RELFUN
end) : Mtp_prover_intf.MTPROVER

module CombiProver (CombiProver__1 : sig
  module MTPGlobal : Mtp_global.MTPGLOBAL

  (*! structure IntSyn' : INTSYN !*)
  module ProverOld : Prover.PROVER

  (*! sharing ProverOld.IntSyn = IntSyn' !*)
  module ProverNew : Mtp_prover_intf.MTPROVER
end) : Mtp_prover_intf.MTPROVER
