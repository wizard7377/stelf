open! Basis
open! Global
open! Global.Global_
open! Intsyn
open! Intsyn.Lambda_
open! Names
open! Names.Names_
open! Paths
open! Paths.Paths_
open! Table
open! Table.Table_
open! Formatter
open! Formatter__Formatter_
open! Print
open! Print.Print_
open! Subordinate
open! Subordinate
open! Modes
open! Modes.Modes_
open! Thm
open! Thm.Thm_
open! Terminate
open! Terminate.Terminate_
open! Index
open! Index.Index_
open! Solvers
open! Solvers.Solvers_
open! Worldcheck
open! Worldcheck.Worldcheck_
open! Typecheck
open! Typecheck.Typecheck_
open! Timing
open! Timing.Timing_
open! Unique
open! Unique.Unique_

(* # 1 "src/cover/Cover_.sig.ml" *)
open! Basis

(* Coverage Checking *)

(** Author: Frank Pfenning *)

module type COVER = sig
  exception Error of string

  val checkNoDef : IntSyn.cid -> unit

  val checkOut : IntSyn.dctx * IntSyn.eclo -> unit
  (** raises Error(msg) *)

  val checkCovers : IntSyn.cid * Modesyn.ModeSyn.modeSpine -> unit

  val coverageCheckCases :
    Tomega.worlds * (IntSyn.dctx * IntSyn.sub) list * IntSyn.dctx -> unit
end
