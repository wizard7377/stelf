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

(* # 1 "src/frontend/ParseThm.sig.ml" *)
open! Basis
open! Parsing

(* Parsing Theorems *)
(* Author: Carsten Schuermann *)

module type PARSE_THM = sig
  (*! structure Parsing : PARSING !*)
  module ThmExtSyn : RECONTHM.THMEXTSYN

  val parseTotal' : ThmExtSyn.tdecl Parsing.parser

  (* -fp *)
  val parseTerminates' : ThmExtSyn.tdecl Parsing.parser
  val parseReduces' : ThmExtSyn.rdecl Parsing.parser

  (* -bp *)
  val parseTabled' : ThmExtSyn.tableddecl Parsing.parser

  (* -bp *)
  val parseKeepTable' : ThmExtSyn.keepTabledecl Parsing.parser

  (* -bp *)
  val parseTheorem' : ThmExtSyn.theorem Parsing.parser
  val parseTheoremDec' : ThmExtSyn.theoremdec Parsing.parser
  val parseWorlds' : ThmExtSyn.wdecl Parsing.parser
  val parseProve' : ThmExtSyn.prove Parsing.parser
  val parseEstablish' : ThmExtSyn.establish Parsing.parser
  val parseAssert' : ThmExtSyn.assert_ Parsing.parser
end
