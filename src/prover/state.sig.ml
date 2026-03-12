open! Basis

(* State definition for Proof Search *)
(* Author: Carsten Schuermann *)
module type STATE = sig
  exception Error of string

  type state_ =
    | State of
        Tomega.worlds_ * Tomega.dec_ IntSyn.ctx_ * Tomega.prg_ * Tomega.for_
    | StateLF of IntSyn.exp_

  type focus_ = Focus of Tomega.prg_ * Tomega.worlds_ | FocusLF of IntSyn.exp_

  (* Focus (EVar, W) *)
  (* focus EVar *)
  val init : Tomega.for_ * Tomega.worlds_ -> state_
  val close : state_ -> bool
  val collectT : Tomega.prg_ -> Tomega.prg_ list
  val collectLF : Tomega.prg_ -> IntSyn.exp_ list
  val collectLFSub : Tomega.sub_ -> IntSyn.exp_ list
end
