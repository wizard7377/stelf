open! Basis
open! Timing
open! Timing.Timing_
open! Stream
open! Stream.Stream_
open! Global
open! Global.Global_
open! Table
open! Table.Table_
open! Tabling
open! Intsyn
open! Intsyn.Lambda_
open! Names
open! Names.Names_
open! Paths
open! Paths.Paths_
open! Print
open! Print.Print_
open! Typecheck
open! Typecheck.Typecheck_
open! Style
open! Style.Style_
open! Modes
open! Modes.Modes_
open! Terminate
open! Terminate.Terminate_
open! Index
open! Index.Index_
open! Thm
open! Thm.Thm_
open! M2
open! M2.M2_
open! Compile
open! Compile.Compile_
open! Opsem
open! Opsem.Opsem_
open! Subordinate
open! Subordinate
open! Modules
open! Modules.Modules_
open! Meta
open! Meta.Meta_
open! Solvers
open! Solvers.Solvers_
open! Worldcheck
open! Worldcheck.Worldcheck_
open! Unique
open! Unique.Unique_
open! Cover
open! Cover.Cover_
open! Tomega_lib
open! Tomega_lib.Tomega_
open! Prover
open! Flit
open! Flit.Flit_
open! Msg
open! Msg.Msg_

(* # 1 "src/frontend/Solve.sig.ml" *)
open! Basis

(* Solve and query declarations, interactive top level *)
(* Author: Frank Pfenning *)

module type SOLVE = sig
  (*! structure IntSyn : INTSYN !*)
  (*! structure Paths : PATHS !*)
  module ExtQuery : RECONQUERY.EXTQUERY

  exception AbortQuery of string

  val solve :
    ExtQuery.define list * ExtQuery.solve * Paths.location ->
    (IntSyn.conDec * Paths.occConDec option) list

  val query :
    (int option * int option * ExtQuery.query) * Paths.location -> unit

  (* may raise AbortQuery(msg) *)
  val querytabled :
    (int option * int option * ExtQuery.query) * Paths.location -> unit

  (* may raise AbortQuery(msg) *)
  val qLoop : unit -> bool

  (* true means normal exit *)
  val qLoopT : unit -> bool
end
