(* # 1 "src/m2/M2_.sig.ml" *)

(* # 1 "src/m2/M2_.fun.ml" *)

(* # 1 "src/m2/M2_.sml.ml" *)
open! Basis
open MetaPrint
open Init
open Search
open Lemma
open Splitting
open Filling
open Recursion
open Qed
open Strategy
open Prover
open Mpi
open Skolem

module MetaSyn = Metasyn.Make_MetaSyn (Whnf)

module MetaAbstract_ = MetaAbstract.MetaAbstract (struct
  module Global = Global
  module MetaSyn = MetaSyn
  module MetaGlobal = MetaGlobal.MetaGlobal
  module Abstract = Abstract
  module ModeTable = ModeTable
  module Whnf = Whnf
  module Print = Print
  module Constraints = Constraints
  module Unify = UnifyNoTrail
  module Names = Names
  module TypeCheck = TypeCheck
  module Subordinate = Subordinate.Subordinate_.Subordinate
end)

(*! structure CsManager = CsManager !*)
module MetaPrint_ = MetaPrint (struct
  module Global = Global
  module MetaSyn' = MetaSyn
  module Formatter = Formatter__Formatter_.Formatter
  module Print = Print
  module ClausePrint = ClausePrint
end)

module Init = Init (struct
  module MetaSyn' = MetaSyn
  module MetaAbstract = MetaAbstract_
end)

module OLDSearch = OLDSearch (struct
  module MetaGlobal = MetaGlobal.MetaGlobal
  module Conv = Conv
  module MetaSyn' = MetaSyn

  (*! structure CompSyn' = CompSyn !*)
  module Compile = Compile_.Compile
  module Whnf = Whnf
  module Unify = UnifyTrail
  module Index = Index

  (* structure Assign = Assign *)
  module CPrint = CPrint
  module Print = Print
  module Names = Names
end)

(*! structure CsManager = CsManager !*)
module Lemma = Lemma (struct
  module MetaSyn' = MetaSyn
  module MetaAbstract = MetaAbstract_
end)

module Splitting = Splitting (struct
  module Global = Global
  module MetaSyn' = MetaSyn
  module MetaPrint = MetaPrint_
  module MetaAbstract = MetaAbstract_
  module Whnf = Whnf
  module ModeTable = ModeTable
  module Index = Index
  module Print = Print
  module Unify = UnifyTrail
end)

(*! structure CsManager = CsManager !*)
module Filling = Filling (struct
  module Global = Global
  module MetaSyn' = MetaSyn
  module MetaAbstract = MetaAbstract_
  module Print = Print
  module Search = OLDSearch
  module Whnf = Whnf
end)

module Recursion = Recursion (struct
  module Global = Global
  module MetaGlobal = MetaGlobal.MetaGlobal
  module MetaSyn' = MetaSyn
  module MetaPrint = MetaPrint_
  module Whnf = Whnf
  module Unify = UnifyTrail
  module Conv = Conv
  module Names = Names
  module Print = Print
  module Subordinate = Subordinate.Subordinate_.Subordinate
  module Order = Order
  module ModeTable = ModeTable
  module MetaAbstract = MetaAbstract_
  module Lemma = Lemma
  module Filling = Filling
  module Formatter = Formatter
end)

(*! structure CsManager = CsManager !*)
module Qed = Qed (struct
  module Global = Global
  module MetaSyn' = MetaSyn
end)

module StrategyFRS = StrategyFRS (struct
  module MetaGlobal = MetaGlobal.MetaGlobal
  module MetaSyn' = MetaSyn
  module MetaAbstract = MetaAbstract_
  module Lemma = Lemma
  module Filling = Filling
  module Recursion = Recursion
  module Splitting = Splitting
  module Qed = Qed
  module MetaPrint = MetaPrint_
  module Timers = Timers.Timers
end)

module StrategyRFS = StrategyRFS (struct
  module MetaGlobal = MetaGlobal.MetaGlobal
  module MetaSyn' = MetaSyn
  module MetaAbstract = MetaAbstract_
  module Lemma = Lemma
  module Filling = Filling
  module Recursion = Recursion
  module Splitting = Splitting
  module Qed = Qed
  module MetaPrint = MetaPrint_
  module Timers = Timers.Timers
end)

module Strategy = Strategy (struct
  module MetaGlobal = MetaGlobal.MetaGlobal
  module MetaSyn' = MetaSyn
  module StrategyFRS = StrategyFRS
  module StrategyRFS = StrategyRFS
end)

module Prover = Prover (struct
  module MetaGlobal = MetaGlobal.MetaGlobal
  module MetaSyn' = MetaSyn
  module MetaAbstract = MetaAbstract_
  module MetaPrint = MetaPrint_
  module Filling = Filling
  module Splitting = Splitting
  module Recursion = Recursion
  module Init = Init
  module Strategy = Strategy
  module Qed = Qed
  module Names = Names
  module Timers = Timers.Timers
end)

module M2Prover = Prover

module Mpi = Mpi (struct
  module MetaGlobal = MetaGlobal.MetaGlobal
  module MetaSyn' = MetaSyn
  module MetaAbstract = MetaAbstract_
  module Init = Init
  module Lemma = Lemma
  module Filling = Filling
  module Recursion = Recursion
  module Splitting = Splitting
  module Strategy = Strategy
  module Qed = Qed
  module MetaPrint = MetaPrint_
  module Names = Names
  module Timers = Timers.Timers
  module Ring = Ring.Ring
end)

module IndexSkolem = IndexSkolem.MakeIndexSkolem (Global) (Queue.Queue)

module Skolem = Skolem (struct
  module Global = Global

  (*! structure IntSyn' = IntSyn !*)
  module Whnf = Whnf
  module Abstract = Abstract
  module IndexSkolem = IndexSkolem
  module ModeTable = ModeTable
  module Print = Print
  module Timers = Timers.Timers
  module Compile = Compile
  module Names = Names
end)

module type PROVER = Prover_intf.PROVER
