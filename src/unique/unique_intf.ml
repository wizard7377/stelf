(* # 1 "src/unique/unique_.sig.ml" *)
open! Basis

(* Uniqueness Checking *)

(** Author: Frank Pfenning *)

module type UNIQUE = sig
  exception Error of string

  val checkUnique : IntSyn.cid * Modesyn.ModeSyn.modeSpine -> unit
end
