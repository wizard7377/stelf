open! Basis

(* Meta Prover Version 1.3 *)
(* Author: Carsten Schuermann *)
module type MTPROVER = sig
  (*! structure FunSyn : FUNSYN !*)
  module StateSyn : STATESYN

  exception Error of string

  val init : FunSyn.for_ * StateSyn.order_ -> unit
end
(* signature MTPROVER *)
