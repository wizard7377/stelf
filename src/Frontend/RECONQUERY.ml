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

(* # 1 "src/frontend/ReconQuery.sig.ml" *)
open! Basis

(* External Syntax for queries *)
(* Author: Frank Pfenning *)

module type EXTQUERY = sig
  module ExtSyn : RECONTERM.EXTSYN

  (*! structure Paths : PATHS !*)
  type query

  (* query *)
  val query : string option * ExtSyn.term -> query

  (* ucid : tm | tm *)
  type define

  val define : string option * ExtSyn.term * ExtSyn.term option -> define

  type solve

  val solve : string option * ExtSyn.term * Paths.region -> solve
end

module type RECON_QUERY = sig
  (*! structure IntSyn : INTSYN !*)
  include EXTQUERY

  exception Error of string

  val queryToQuery :
    query * Paths.location ->
    IntSyn.exp * string option * (IntSyn.exp * string) list

  (* (A, SOME(""X""), [(Y1, ""Y1""),...] *)
  (* where A is query type, X the optional proof term variable name *)
  (* Yi the EVars in the query and ""Yi"" their names *)
  val solveToSolve :
    define list * solve * Paths.location ->
    IntSyn.exp * (IntSyn.exp -> (IntSyn.conDec * Paths.occConDec option) list)
end
