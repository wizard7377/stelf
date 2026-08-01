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

(* # 1 "src/meta/Mpi.sig.ml" *)
open! Basis
open Funsyn
open Statesyn
open MtpGlobal
open Relfun
open Funtypecheck
open MtpData
open MtpInit
open MtpFilling
open Inference
open MtpSplitting
open MtpRecursion
open MtpStrategy
open MtpPrint
open Timers
open Ring

(* Meta Prover Interface *)
(* Author: Carsten Schuermann *)

module type MTPI = sig
  (*! structure FunSyn : FUNSYN !*)
  module StateSyn : STATESYN

  exception Error of string

  val init : int -> string list -> unit
  val select : int -> unit
  val print : unit -> unit
  val next : unit -> unit
  val auto : unit -> unit
  val solve : unit -> unit
  val check : unit -> unit
  val reset : unit -> unit

  (*  val extract: unit -> MetaSyn.Sgn *)
  (*  val show   : unit -> unit *)
  val undo : unit -> unit
end
