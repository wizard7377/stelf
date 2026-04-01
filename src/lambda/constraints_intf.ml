(* # 1 "src/lambda/constraints.sig.ml" *)

open! Basis
(** Constraint simplification and reporting helpers for LF terms. *)

open Intsyn

(* Manipulating Constraints *)
(* Author: Jeff Polakow, Frank Pfenning *)
(* Modified: Roberto Virga *)

module type CONSTRAINTS = sig
  (*! structure IntSyn : INTSYN !*)
  exception Error of IntSyn.cnstr list

  val simplify : IntSyn.cnstr list -> IntSyn.cnstr list

  val warn_constraints : string list -> unit
  (** Report unresolved constraint owners in a human-readable form. *)

  val warnConstraints : string list -> unit
  (** Compatibility alias for {!warn_constraints}. *)
end
