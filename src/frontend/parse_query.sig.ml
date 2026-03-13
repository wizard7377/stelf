open! Basis
open! Parsing

(* Parsing Queries *)
(* Author: Frank Pfenning *)
module type PARSE_QUERY = sig
  (*! structure Parsing : PARSING !*)
  module ExtQuery : Recon_query.EXTQUERY

  val parseQuery' : ExtQuery.query Parsing.parser
  val parseSolve' : (ExtQuery.define list * ExtQuery.solve) Parsing.parser
end
(* signature PARSE_QUERY *)
