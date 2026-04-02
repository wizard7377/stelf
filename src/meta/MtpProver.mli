include module type of MtpProver_intf

module MTProver (MTProver__0 : sig
  module MTPGlobal : MtpGlobal.MTPGLOBAL

  (*! structure IntSyn' : INTSYN !*)
  (*! structure FunSyn : FUNSYN !*)
  (*! sharing FunSyn.IntSyn = IntSyn' !*)
  module StateSyn : Statesyn_intf.STATESYN

  (*! sharing IntSyn = IntSyn' !*)
  (*! sharing StateSyn.FunSyn = FunSyn !*)
  module Order : ORDER

  (*! sharing Order.IntSyn = IntSyn' !*)
  module MTPInit : MtpInit_intf.MTPINIT

  (*! sharing MTPInit.FunSyn = FunSyn !*)
  module MTPStrategy : MtpStrategy_intf.MTPSTRATEGY
  module RelFun : Relfun_intf.RELFUN
end) : MtpProver_intf.MTPROVER

module CombiProver (CombiProver__1 : sig
  module MTPGlobal : MtpGlobal.MTPGLOBAL

  (*! structure IntSyn' : INTSYN !*)
  module ProverOld : Prover.PROVER

  (*! sharing ProverOld.IntSyn = IntSyn' !*)
  module ProverNew : MtpProver_intf.MTPROVER
end) : MtpProver_intf.MTPROVER
