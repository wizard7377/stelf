open! Basis
open Funsyn

(* State definition for Proof Search *)
(* Author: Carsten Schuermann *)
module type STATESYN = sig
  (*! structure IntSyn : INTSYN !*)
  (*! structure FunSyn : FUNSYN !*)
  type order_ =
    | Arg of (IntSyn.exp_ * IntSyn.sub_) * (IntSyn.exp_ * IntSyn.sub_)
    | Lex of order_ list
    | Simul of order_ list
    | All of IntSyn.dec_ * order_
    | And of order_ * order_

  (* Orders                     *)
  (* O ::= U[s] : V[s]          *)
  (*     | (O1 .. On)           *)
  (*     | {O1 .. On}           *)
  (*     | {{D}} O              *)
  (*     | O1 ^ O2              *)
  type info_ = Splits of int | Rl | RLdone
  type tag_ = Parameter of FunSyn.label option | Lemma of info_ | None

  type state_ =
    | State of
        int
        * (IntSyn.dctx * tag_ IntSyn.ctx_)
        * (FunSyn.for_ * order_)
        * int
        * order_
        * (int * FunSyn.for_) list
        * FunSyn.for_

  (* History of residual lemmas *)
  (* Current order *)
  (* length of meta context            *)
  (* Induction hypothesis, order       *)
  (* Status information *)
  (* Context of Hypothesis, in general not named *)
  (* Part of theorem                   *)

  (* S = <n, (G, B), (IH, OH), d, O, H, F> *)
  (* Formula *)
  val orderSub : order_ * IntSyn.sub_ -> order_
  val decrease : tag_ -> tag_
  val splitDepth : info_ -> int
  val normalizeOrder : order_ -> order_
  val convOrder : order_ * order_ -> bool
  val normalizeTag : tag_ * IntSyn.sub_ -> tag_
end
(* signature STATESYN *)
