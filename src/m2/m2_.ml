(* # 1 "src/m2/m2_.sig.ml" *)

(* # 1 "src/m2/m2_.fun.ml" *)

(* # 1 "src/m2/m2_.sml.ml" *)
open! Basis
open Meta_print
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

module MetaSyn = Metasyn.Make_MetaSyn (struct
  (*! structure IntSyn' = IntSyn !*) module Whnf = Whnf
end)

module MetaAbstract = Meta_abstract.MetaAbstract (struct
  module Global = Global
  module MetaSyn = MetaSyn
  module MetaGlobal = Meta_global.MetaGlobal
  module Abstract = Abstract
  module ModeTable = ModeTable
  module Whnf = Whnf
  module Print = Print
  module Constraints = Constraints
  module Unify = UnifyNoTrail
  module Names = Names
  module TypeCheck = TypeCheck
  module Subordinate = Subordinate
end)

(*! structure Cs_manager = Cs_manager !*)
module MetaPrint = MetaPrint (struct
  module Global = Global
  module MetaSyn' = MetaSyn
  module Formatter = Formatter
  module Print = Print
  module ClausePrint = ClausePrint
end)

module Init = Init (struct
  module MetaSyn' = MetaSyn
  module MetaAbstract = MetaAbstract
end)

module OLDSearch = OLDSearch (struct
  module MetaGlobal = Meta_global.MetaGlobal
  module Conv = Conv
  module MetaSyn' = MetaSyn

  (*! structure CompSyn' = CompSyn !*)
  module Compile = Compile
  module Whnf = Whnf
  module Unify = UnifyTrail
  module Index = Index

  (* structure Assign = Assign *)
  module CPrint = CPrint
  module Print = Print
  module Names = Names
end)

(*! structure Cs_manager = Cs_manager !*)
module Lemma = Lemma (struct
  module MetaSyn' = MetaSyn
  module MetaAbstract = MetaAbstract
end)

module Splitting = Splitting (struct
  module Global = Global
  module MetaSyn' = MetaSyn
  module MetaPrint = MetaPrint
  module MetaAbstract = MetaAbstract
  module Whnf = Whnf
  module ModeTable = ModeTable
  module Index = Index
  module Print = Print
  module Unify = UnifyTrail
end)

(*! structure Cs_manager = Cs_manager !*)
module Filling = Filling (struct
  module Global = Global
  module MetaSyn' = MetaSyn
  module MetaAbstract = MetaAbstract
  module Print = Print
  module Search = OLDSearch
  module Whnf = Whnf
end)

module Recursion = Recursion (struct
  module Global = Global
  module MetaGlobal = Meta_global.MetaGlobal
  module MetaSyn' = MetaSyn
  module MetaPrint = MetaPrint
  module Whnf = Whnf
  module Unify = UnifyTrail
  module Conv = Conv
  module Names = Names
  module Print = Print
  module Subordinate = Subordinate
  module Order = Order
  module ModeTable = ModeTable
  module MetaAbstract = MetaAbstract
  module Lemma = Lemma
  module Filling = Filling
  module Formatter = Formatter
end)

(*! structure Cs_manager = Cs_manager !*)
module Qed = Qed (struct
  module Global = Global
  module MetaSyn' = MetaSyn
end)

module StrategyFRS = StrategyFRS (struct
  module MetaGlobal = Meta_global.MetaGlobal
  module MetaSyn' = MetaSyn
  module MetaAbstract = MetaAbstract
  module Lemma = Lemma
  module Filling = Filling
  module Recursion = Recursion
  module Splitting = Splitting
  module Qed = Qed
  module MetaPrint = MetaPrint
  module Timers = Timers.Timers
end)

module StrategyRFS = StrategyRFS (struct
  module MetaGlobal = Meta_global.MetaGlobal
  module MetaSyn' = MetaSyn
  module MetaAbstract = MetaAbstract
  module Lemma = Lemma
  module Filling = Filling
  module Recursion = Recursion
  module Splitting = Splitting
  module Qed = Qed
  module MetaPrint = MetaPrint
  module Timers = Timers.Timers
end)

module Strategy = Strategy (struct
  module MetaGlobal = Meta_global.MetaGlobal
  module MetaSyn' = MetaSyn
  module StrategyFRS = StrategyFRS
  module StrategyRFS = StrategyRFS
end)

module Prover = Prover (struct
  module MetaGlobal = Meta_global.MetaGlobal
  module MetaSyn' = MetaSyn
  module MetaAbstract = MetaAbstract
  module MetaPrint = MetaPrint
  module Filling = Filling
  module Splitting = Splitting
  module Recursion = Recursion
  module Init = Init
  module Strategy = Strategy
  module Qed = Qed
  module Names = Names
  module Timers = Timers.Timers
end)

module Mpi = Mpi (struct
  module MetaGlobal = Meta_global.MetaGlobal
  module MetaSyn' = MetaSyn
  module MetaAbstract = MetaAbstract
  module Init = Init
  module Lemma = Lemma
  module Filling = Filling
  module Recursion = Recursion
  module Splitting = Splitting
  module Strategy = Strategy
  module Qed = Qed
  module MetaPrint = MetaPrint
  module Names = Names
  module Timers = Timers.Timers
  module Ring = Ring.Ring
end)

module IndexSkolem = Index_skolem.MakeIndexSkolem (struct
  module Global = Global
  module Queue = Queue
end)

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

module type PROVER = PROVER
