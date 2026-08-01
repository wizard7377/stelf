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

(* # 1 "src/meta/Prover.sig.ml" *)
open! Basis
open Funsyn
open Statesyn
open MtpGlobal
open MtpInit
open MtpStrategy
open Relfun

(* Meta Prover Version 1.3 *)
(* Author: Carsten Schuermann *)

module type MTPROVER = sig
  exception Error of string

  val init : int -> IntSyn.cid list -> unit
  val auto : unit -> unit
  val print : unit -> unit
  val install : (IntSyn.conDec -> IntSyn.cid) -> unit
end
