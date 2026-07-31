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

(* # 1 "src/frontend/Frontend_.sig.ml" *)

(* # 1 "src/frontend/Frontend_.fun.ml" *)

(* # 1 "src/frontend/Frontend_.sml.ml" *)
open! Basis

(* Front End Interface *)
(* Author: Frank Pfenning *)
(* Presently, we do not memoize the token stream returned *)
(* by the Lexer.  Use Stream = MStream below if memoization becomes *)
(* necessary. *)
(* Now in Lexer.fun *)
(*
structure Lexer =
  Lexer (structure Stream' = Stream
	 structure Paths' = Paths);
*)
(* Now in Parsing.fun *)
(*
structure Parsing =
  Parsing (structure Stream' = Stream
	   structure Lexer' = Lexer);
*)
(* Re-export module type before Stelf name shadowing. *)
module type LEXER = Lexer.LEXER
module type STELF = Twelf_.STELF

module ReconTerm : RECONTERM.RECON_TERM
module ReconConDec : RECONCONDEC.RECON_CONDEC
module ReconQuery : RECONQUERY.RECON_QUERY
module ReconMode : RECONMODE.RECON_MODE
module ReconThm : RECONTHM.RECON_THM
module ReconModule : RECONMODULE.RECON_MODULE
module ParseTerm : PARSETERM.PARSE_TERM

module ParseTermConDec :
  PARSETERM.PARSE_TERM with module ExtSyn = ReconConDec.ExtSyn

module ParseTermQuery :
  PARSETERM.PARSE_TERM with module ExtSyn = ReconQuery.ExtSyn

module ParseTermMode :
  PARSETERM.PARSE_TERM with module ExtSyn = ReconMode.ExtSyn

module ParseTermThm : PARSETERM.PARSE_TERM with module ExtSyn = ReconThm.ExtSyn

module ParseTermModule :
  PARSETERM.PARSE_TERM with module ExtSyn = ReconModule.ExtSyn

module ParseConDec : PARSECONDEC.PARSE_CONDEC
module ParseQuery : PARSEQUERY.PARSE_QUERY
module ParseFixity : PARSEFIXITY.PARSE_FIXITY with module Names = Names
module ParseMode : PARSEMODE.PARSE_MODE
module ParseThm : PARSETHM.PARSE_THM
module ParseModule : PARSEMODULE.PARSE_MODULE
module Parser : PARSER.PARSER
module Solve : SOLVE.SOLVE with module ExtQuery = ReconQuery
module Fquery : FQUERY.FQUERY with module ExtQuery = ReconQuery
module Stelf : STELF
