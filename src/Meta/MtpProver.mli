open! Basis
open! Global
open! Global.Global_
open! Trail
open! Trail.Trail_
open! Table
open! Table.Table_
open! Intsyn
open! Intsyn.Lambda_
open! Names
open! Names.Names_
open! Formatter
open! Formatter__Formatter_
open! Print
open! Print.Print_
open! Subordinate
open! Subordinate
open! Modes
open! Modes.Modes_
open! Typecheck
open! Typecheck.Typecheck_
open! Index
open! Index.Index_
open! Opsem
open! Opsem.Opsem_
open! Compile
open! Compile.Compile_
open! Heuristic
open! Heuristic.Heuristic_
open! Timing
open! Timing.Timing_
open! Solvers
open! Solvers.Solvers_
open! M2
open! M2.M2_
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
