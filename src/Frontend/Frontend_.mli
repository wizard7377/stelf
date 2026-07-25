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
