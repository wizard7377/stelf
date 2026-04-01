(* # 1 "src/frontend/parse_fixity.sig.ml" *)
open! Basis
open! Parsing

(* Parsing Fixity Declarations *)
(* Author: Frank Pfenning *)

module type PARSE_FIXITY = sig
  (*! structure Parsing : PARSING !*)
  module Names : NAMES

  val parseFixity' :
    ((Names.qid * Paths.region) * Names.Fixity.fixity) Parsing.parser

  val parseNamePref' :
    ((Names.qid * Paths.region) * (string list * string list)) Parsing.parser
end
