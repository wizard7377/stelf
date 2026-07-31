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

(* # 1 "src/frontend/ParseTerm.sig.ml" *)
open! Basis
open! Parsing

(* Parsing Terms and Declarations *)
(* Author: Frank Pfenning *)

module type PARSE_TERM = sig
  (*! structure Parsing : PARSING !*)
  module ExtSyn : RECONTERM.EXTSYN

  val parseQualId' : (string list * Parsing.lexResult) Parsing.parser
  val parseQualIds' : (string list * string) list Parsing.parser
  val parseFreeze' : (string list * string) list Parsing.parser

  val parseSubord' :
    ((string list * string) * (string list * string)) list Parsing.parser

  val parseThaw' : (string list * string) list Parsing.parser
  val parseDeterministic' : (string list * string) list Parsing.parser
  val parseCompile' : (string list * string) list Parsing.parser

  (* -ABP 4/4/03 *)
  val parseTerm' : ExtSyn.term Parsing.parser
  val parseDec' : (string option * ExtSyn.term option) Parsing.parser
  val parseCtx' : ExtSyn.dec list Parsing.parser
end
