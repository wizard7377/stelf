(* # 1 "src/frontend/frontend_.sig.ml" *)

(* # 1 "src/frontend/frontend_.fun.ml" *)

(* # 1 "src/frontend/frontend_.sml.ml" *)
open! Basis

(* Front End Interface *)
(* Author: Frank Pfenning *)
(* Presently, we do not memoize the token stream returned *)
(* by the lexer.  Use Stream = MStream below if memoization becomes *)
(* necessary. *)
(* Now in lexer.fun *)
(*
structure Lexer =
  Lexer (structure Stream' = Stream
	 structure Paths' = Paths);
*)
(* Now in parsing.fun *)
(*
structure Parsing =
  Parsing (structure Stream' = Stream
	   structure Lexer' = Lexer);
*)
(* Re-export module type before Stelf name shadowing. *)
module type LEXER = Lexer.LEXER
module type STELF = Twelf_.STELF

module ReconTerm : Recon_term.RECON_TERM

module ReconConDec : Recon_condec.RECON_CONDEC

module ReconQuery : Recon_query.RECON_QUERY

module ReconMode : Recon_mode.RECON_MODE

module ReconThm : Recon_thm.RECON_THM

module ReconModule : Recon_module.RECON_MODULE

module ParseTerm : Parse_term.PARSE_TERM

module ParseTermConDec :
  Parse_term.PARSE_TERM with module ExtSyn = ReconConDec.ExtSyn

module ParseTermQuery :
  Parse_term.PARSE_TERM with module ExtSyn = ReconQuery.ExtSyn

module ParseTermMode :
  Parse_term.PARSE_TERM with module ExtSyn = ReconMode.ExtSyn

module ParseTermThm :
  Parse_term.PARSE_TERM with module ExtSyn = ReconThm.ExtSyn

module ParseTermModule :
  Parse_term.PARSE_TERM with module ExtSyn = ReconModule.ExtSyn

module ParseConDec : Parse_condec.PARSE_CONDEC

module ParseQuery : Parse_query.PARSE_QUERY

module ParseFixity : Parse_fixity.PARSE_FIXITY with module Names = Names

module ParseMode : Parse_mode.PARSE_MODE

module ParseThm : Parse_thm.PARSE_THM

module ParseModule : Parse_module.PARSE_MODULE

module Parser : Parser_intf.PARSER

module Solve : Solve_intf.SOLVE with module ExtQuery = ReconQuery

module Fquery : Fquery_intf.FQUERY with module ExtQuery = ReconQuery

module Stelf : STELF
