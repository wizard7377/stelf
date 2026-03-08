open! Basis

(* Parsing Fixity Declarations *)
(* Author: Frank Pfenning *)
module type PARSE_FIXITY = sig
  (*! structure Parsing : PARSING !*)
  module Names : NAMES

  val parseFixity' :
    ((Names.qid_ * Paths.region) * Names.Fixity.fixity) Parsing.parser

  val parseNamePref' :
    ((Names.qid_ * Paths.region) * (string list * string list)) Parsing.parser
end
(* signature PARSE_FIXITY *)
