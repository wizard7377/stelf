(* # 1 "src/meta/Statesyn.sig.ml" *)
open! Basis
open Funsyn

(* State definition for Proof Search *)
(* Author: Carsten Schuermann *)

module type STATESYN = sig
  (*! structure IntSyn : INTSYN !*)
  (*! structure FunSyn : FUNSYN !*)
  type order =
    | Arg of (IntSyn.exp * IntSyn.sub) * (IntSyn.exp * IntSyn.sub)
    | Lex of order list
    | Simul of order list
    | All of IntSyn.dec * order
    | And of order * order

  (* Orders                     *)
  (* O ::= U[s] : V[s]          *)
  (*     | (O1 .. On)           *)
  (*     | {O1 .. On}           *)
  (*     | {{D}} O              *)
  (*     | O1 ^ O2              *)
  type info = Splits of int | Rl | RLdone
  type tag = Parameter of FunSyn.label option | Lemma of info | None

  type state =
    | State of
        int
        * (IntSyn.dctx * tag IntSyn.ctx)
        * (FunSyn.for_ * order)
        * int
        * order
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
  val orderSub : order * IntSyn.sub -> order
  val decrease : tag -> tag
  val splitDepth : info -> int
  val normalizeOrder : order -> order
  val convOrder : order * order -> bool
  val normalizeTag : tag * IntSyn.sub -> tag
end
