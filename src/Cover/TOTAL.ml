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

(* # 1 "src/cover/Total.sig.ml" *)
open! Basis

(* Total Declarations *)
(* Author: Frank Pfenning *)

module type TOTAL = sig
  (*! structure IntSyn : INTSYN !*)
  exception Error of string

  val reset : unit -> unit
  val install : IntSyn.cid -> unit

  (* install(a) --- a is total in its input arguments *)
  val uninstall : IntSyn.cid -> bool

  (* true: was known to be total *)
  val checkFam : IntSyn.cid -> unit
end

module type COVER = sig
  exception Error of string

  val checkNoDef : IntSyn.cid -> unit
  val checkOut : IntSyn.dctx * IntSyn.eclo -> unit
  val checkCovers : IntSyn.cid * Modesyn.ModeSyn.modeSpine -> unit

  val coverageCheckCases :
    Tomega.worlds * (IntSyn.dctx * IntSyn.sub) list * IntSyn.dctx -> unit
end
