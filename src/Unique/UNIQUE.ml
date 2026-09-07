open! Intsyn.Lambda_
open! Modes

(* # 1 "src/unique/Unique_.sig.ml" *)
open! Basis

(* Uniqueness Checking *)

(** Author: Frank Pfenning *)

module type UNIQUE = sig
  exception Error of string

  val checkUnique : IntSyn.cid -> Modesyn.ModeSyn.modeSpine -> unit
end
