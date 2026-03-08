open! Basis

(* fquery: Executing logic programs via functional interpretation *)
(* Author: Carsten Schuermann *)
module type FQUERY = sig
  module ExtQuery : EXTQUERY

  exception AbortQuery of string

  val run : ExtQuery.query * Paths.location -> unit
end
(* may raise AbortQuery(msg) *)
(* signature SOLVE *)
