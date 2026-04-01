(* # 1 "src/frontend/recon_query.sig.ml" *)
open! Basis

(* External Syntax for queries *)
(* Author: Frank Pfenning *)

module type EXTQUERY = sig
  module ExtSyn : Recon_term.EXTSYN

  (*! structure Paths : PATHS !*)
  type query

  (* query *)
  val query : string option * ExtSyn.term -> query

  (* ucid : tm | tm *)
  type define

  val define : string option * ExtSyn.term * ExtSyn.term option -> define

  type solve

  val solve : string option * ExtSyn.term * Paths.region -> solve
end

module type RECON_QUERY = sig
  (*! structure IntSyn : INTSYN !*)
  include EXTQUERY

  exception Error of string

  val queryToQuery :
    query * Paths.location ->
    IntSyn.exp * string option * (IntSyn.exp * string) list

  (* (A, SOME(""X""), [(Y1, ""Y1""),...] *)
  (* where A is query type, X the optional proof term variable name *)
  (* Yi the EVars in the query and ""Yi"" their names *)
  val solveToSolve :
    define list * solve * Paths.location ->
    IntSyn.exp * (IntSyn.exp -> (IntSyn.conDec * Paths.occConDec option) list)
end
