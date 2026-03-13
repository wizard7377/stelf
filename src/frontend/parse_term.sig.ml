open! Basis
open! Parsing

(* Parsing Terms and Declarations *)
(* Author: Frank Pfenning *)
module type PARSE_TERM = sig
  (*! structure Parsing : PARSING !*)
  module ExtSyn : Recon_term.EXTSYN

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
(* signature PARSE_TERM *)
