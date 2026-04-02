(* # 1 "src/frontend/ParseCondec.sig.ml" *)
open! Basis
open! Parsing

(* Parsing Signature Entries *)
(* Author: Frank Pfenning *)

module type PARSE_CONDEC = sig
  (*! structure Parsing : PARSING !*)
  module ExtConDec : ReconCondec_intf.EXTCONDEC

  val parseConDec' : ExtConDec.condec Parsing.parser
  val parseAbbrev' : ExtConDec.condec Parsing.parser
  val parseClause' : ExtConDec.condec Parsing.parser
end
