(* # 1 "src/prover/elim.sig.ml" *)
open! Basis

(* ELIM: Version 1.4 *)
(* Author: Carsten Schuermann *)

module type ELIM = sig
  module State : State.STATE

  exception Error of string

  type operator

  val expand : State.focus -> operator list
  val apply : operator -> unit
  val menu : operator -> string
end
