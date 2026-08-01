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

(* # 1 "src/meta/Splitting.sig.ml" *)
open! Basis
open Funsyn
open Statesyn
open MtpGlobal
open MtpAbstract
open MtpPrint
open Funtypecheck

(* Splitting : Version 1.3 *)
(* Author: Carsten Schuermann *)

module type MTPSPLITTING = sig
  module StateSyn : STATESYN

  exception Error of string

  type operator

  val expand : StateSyn.state -> operator list
  val applicable : operator -> bool
  val apply : operator -> StateSyn.state list
  val menu : operator -> string
  val index : operator -> int
  val compare : operator -> operator -> order
end
