open! Basis

(* Parsing Signature Entries *)
(* Author: Frank Pfenning *)
module type PARSE_CONDEC = sig
  (*! structure Parsing : PARSING !*)
  module ExtConDec : EXTCONDEC

  val parseConDec' : ExtConDec.condec Parsing.parser
  val parseAbbrev' : ExtConDec.condec Parsing.parser
  val parseClause' : ExtConDec.condec Parsing.parser
end
(* signature PARSE_CONDEC *)
