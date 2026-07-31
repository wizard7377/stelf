open! Basis
open! Stream
open! Stream.Stream_
open! Global
open! Global.Global_
open! Intsyn
open! Intsyn.Lambda_
open! Names
open! Names.Names_
open! Modes
open! Modes.Modes_
open! Paths
open! Paths.Paths_
open! Formatter
open! Formatter__Formatter_
open! Print
open! Print.Print_
open! Typecheck
open! Typecheck.Typecheck_
open! Terminate
open! Terminate.Terminate_
open! Index
open! Index.Index_
open! Thm
open! Thm.Thm_
open! Opsem
open! Opsem.Opsem_
open! Compile
open! Compile.Compile_
open! Subordinate
open! Subordinate
open! Table
open! Table.Table_
open! Timing
open! Timing.Timing_
open! Solvers
open! Solvers.Solvers_

(* # 1 "src/m2/MetaPrint.sig.ml" *)
open! Basis
open Metasyn

(* Meta printer for proof states *)
(* Author: Carsten Schuermann *)

module type METAPRINT = sig
  module MetaSyn : Metasyn.METASYN

  val stateToString : MetaSyn.state -> string
  val sgnToString : MetaSyn.sgn -> string
  val modeToString : MetaSyn.mode -> string
  val conDecToString : IntSyn.conDec -> string
end
