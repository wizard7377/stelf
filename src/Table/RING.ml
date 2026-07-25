(* # 1 "src/table/Ring.sig.ml" *)

(** Cyclic list (ring) operations and traversal helpers. *)

open Basis

(* Rings (aka cyclic lists) *)
(* Author: Carsten Schuermann *)

module type RING = sig
  exception Empty

  type 'a ring

  val init : 'a list -> 'a ring
  val empty : 'a ring -> bool
  val insert : 'a ring * 'a -> 'a ring
  val delete : 'a ring -> 'a ring
  val current : 'a ring -> 'a
  val next : 'a ring -> 'a ring
  val previous : 'a ring -> 'a ring
  val foldr : ('a * 'b -> 'b) -> 'b -> 'a ring -> 'b
  val map : ('a -> 'b) -> 'a ring -> 'b ring
end
