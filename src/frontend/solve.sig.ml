open! Basis

(* Solve and query declarations, interactive top level *)
(* Author: Frank Pfenning *)
module type SOLVE = sig
  (*! structure IntSyn : INTSYN !*)
  (*! structure Paths : PATHS !*)
  module ExtQuery : EXTQUERY

  exception AbortQuery of string

  val solve :
    ExtQuery.define list * ExtQuery.solve * Paths.location ->
    (IntSyn.conDec_ * Paths.occConDec option) list

  val query :
    (int option * int option * ExtQuery.query) * Paths.location -> unit

  (* may raise AbortQuery(msg) *)
  val querytabled :
    (int option * int option * ExtQuery.query) * Paths.location -> unit

  (* may raise AbortQuery(msg) *)
  val qLoop : unit -> bool

  (* true means normal exit *)
  val qLoopT : unit -> bool
end
(* true means normal exit *)
(* signature SOLVE *)
