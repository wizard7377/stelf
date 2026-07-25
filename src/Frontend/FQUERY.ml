(* # 1 "src/frontend/Fquery.sig.ml" *)
open! Basis

(* fquery: Executing logic programs via functional interpretation *)
(* Author: Carsten Schuermann *)

module type FQUERY = sig
  module ExtQuery : RECONQUERY.EXTQUERY

  exception AbortQuery of string

  val run : ExtQuery.query * Paths.location -> unit
end
