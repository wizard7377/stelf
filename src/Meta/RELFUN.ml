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
open! Basis
open Modetable
open Funweaken
open Funnames
open Funsyn

(* Converter from relational representation to a functional
   representation of proof terms *)
(* Author: Carsten Schuermann *)
module type RELFUN = sig
  (*! structure FunSyn : FUNSYN !*)
  exception Error of string

  val convertFor : IntSyn.cid list -> FunSyn.for_
  val convertPro : IntSyn.cid list -> FunSyn.pro
end
