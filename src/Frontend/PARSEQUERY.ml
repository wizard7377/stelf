(* # 1 "src/frontend/ParseQuery.sig.ml" *)
open! Basis
open! Parsing

(* Parsing Queries *)
(* Author: Frank Pfenning *)

module type PARSE_QUERY = sig
  (*! structure Parsing : PARSING !*)
  module ExtQuery : RECONQUERY.EXTQUERY

  val parseQuery' : ExtQuery.query Parsing.parser
  val parseSolve' : (ExtQuery.define list * ExtQuery.solve) Parsing.parser
end
