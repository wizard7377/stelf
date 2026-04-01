(* # 1 "src/prover/split.sig.ml" *)
open! Basis

(* Splitting: Version 1.4 *)
(* Author: Carsten Schuermann *)

module type SPLIT = sig
  (*! structure IntSyn : INTSYN !*)
  (*! structure Tomega : TOMEGA !*)
  module State : State.STATE

  exception Error of string

  type operator

  val expand : State.focus -> operator list
  val apply : operator -> unit
  val menu : operator -> string
end
