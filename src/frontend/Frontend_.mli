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

module ReconTerm : ReconTerm_intf.RECON_TERM

module ReconConDec : ReconCondec_intf.RECON_CONDEC

module ReconQuery : ReconQuery_intf.RECON_QUERY

module ReconMode : ReconMode_intf.RECON_MODE

module ReconThm : ReconThm_intf.RECON_THM

module ReconModule : ReconModule_intf.RECON_MODULE

module ParseTerm : ParseTerm_intf.PARSE_TERM

module ParseTermConDec :
  ParseTerm_intf.PARSE_TERM with module ExtSyn = ReconConDec.ExtSyn

module ParseTermQuery :
  ParseTerm_intf.PARSE_TERM with module ExtSyn = ReconQuery.ExtSyn

module ParseTermMode :
  ParseTerm_intf.PARSE_TERM with module ExtSyn = ReconMode.ExtSyn

module ParseTermThm :
  ParseTerm_intf.PARSE_TERM with module ExtSyn = ReconThm.ExtSyn

module ParseTermModule :
  ParseTerm_intf.PARSE_TERM with module ExtSyn = ReconModule.ExtSyn

module ParseConDec : ParseCondec_intf.PARSE_CONDEC

module ParseQuery : ParseQuery_intf.PARSE_QUERY

module ParseFixity : ParseFixity_intf.PARSE_FIXITY with module Names = Names

module ParseMode : ParseMode_intf.PARSE_MODE

module ParseThm : ParseThm_intf.PARSE_THM

module ParseModule : ParseModule_intf.PARSE_MODULE

module Parser : Parser_intf.PARSER

module Solve : Solve_intf.SOLVE with module ExtQuery = ReconQuery

module Fquery : Fquery_intf.FQUERY with module ExtQuery = ReconQuery

module Stelf : STELF
