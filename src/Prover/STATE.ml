(* # 1 "src/prover/State.sig.ml" *)
open! Basis

(* State definition for Proof Search *)
(* Author: Carsten Schuermann *)

module type STATE = sig
  exception Error of string

  type state =
    | State of Tomega.worlds * Tomega.dec IntSyn.ctx * Tomega.prg * Tomega.for_
    | StateLF of IntSyn.exp

  type focus = Focus of Tomega.prg * Tomega.worlds | FocusLF of IntSyn.exp

  (* Focus (EVar, W) *)
  (* focus EVar *)
  val init : Tomega.for_ * Tomega.worlds -> state
  val close : state -> bool
  val collectT : Tomega.prg -> Tomega.prg list
  val collectLF : Tomega.prg -> IntSyn.exp list
  val collectLFSub : Tomega.sub -> IntSyn.exp list
end
