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

(* # 1 "src/meta/Funprint.sig.ml" *)
open! Basis
open Funsyn

(* Printing of functional proof terms *)
(* Author: Carsten Schuermann *)

module type FUNPRINT = sig
  (*! structure FunSyn : FUNSYN !*)
  module Formatter : FORMATTER

  val formatForBare : IntSyn.dctx -> FunSyn.for_ -> Formatter.format
  val formatFor : FunSyn.lfctx -> FunSyn.for_ -> string list -> Formatter.format
  val formatPro : FunSyn.lfctx -> FunSyn.pro -> string list -> Formatter.format
  val formatLemmaDec : FunSyn.lemmaDec -> Formatter.format
  val forToString : FunSyn.lfctx -> FunSyn.for_ -> string list -> string
  val proToString : FunSyn.lfctx -> FunSyn.pro -> string list -> string
  val lemmaDecToString : FunSyn.lemmaDec -> string
end
