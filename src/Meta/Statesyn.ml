open! Intsyn.Lambda_

(* # 1 "src/meta/Statesyn.sig.ml" *)
open Funsyn

(* State definition for Proof Search *)
(* Author: Carsten Schuermann *)
include STATESYN
(* signature STATESYN *)

(* # 1 "src/meta/Statesyn.fun.ml" *)
open! Basis

(* State for Proof Search *)
(* Author: Carsten Schuermann *)
module StateSyn (StateSyn__0 : sig
  (*! structure IntSyn' : INTSYN !*)
  (*! structure FunSyn' : FUNSYN !*)
  (*! sharing FunSyn'.IntSyn = IntSyn' !*)
  module Whnf : WHNF

  (*! sharing Whnf.IntSyn = IntSyn' !*)
  module Conv : CONV
end) : STATESYN.STATESYN = struct
  (*! structure IntSyn = IntSyn' !*)
  (*! structure FunSyn = FunSyn' !*)
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
  (* Current Order *)
  (* length of meta context            *)
  (* Induction hypothesis, order       *)
  (* Status information *)
  (* Context of Hypothesis in general not named *)
  (* Part of theorem                   *)

  (* S = <n, (G, B), (IH, OH), d, O, H, F> *)
  (* Formula *)
  open! struct
    module F = FunSyn
    module I = IntSyn

    let rec orderSub a b = match a, b with
      | Arg ((u, s1), (v, s2)), s ->
          Arg ((u, I.comp s1 s), (v, I.comp s2 s))
      | Lex os, s -> Lex (map (function o -> orderSub o s) os)
      | Simul os, s -> Simul (map (function o -> orderSub o s) os)

    let rec normalizeOrder = function
      | Arg (us, vs) ->
          Arg ((Whnf.normalize us, I.id), (Whnf.normalize vs, I.id))
      | Lex os -> Lex (map normalizeOrder os)
      | Simul os -> Simul (map normalizeOrder os)

    let rec convOrder a b = match a, b with
      | Arg (us1, _), Arg (us2, _) -> Conv.conv us1 us2
      | Lex os1, Lex os2 -> convOrders (os1, os2)
      | Simul os1, Simul os2 -> convOrders (os1, os2)

    and convOrders = function
      | [], [] -> true
      | o1 :: l1, o2 :: l2 -> convOrder o1 o2 && convOrders (l1, l2)

    let decreaseInfo = function
      | Splits k -> Splits (k - 1)
      | Rl -> Rl
      | RLdone -> RLdone

    let decrease = function
      | Lemma sp -> Lemma (decreaseInfo sp)
      | None -> None

    let splitDepth (Splits k) = k

    let normalizeTag a b = match a, b with
      | (Parameter _ as t), _ -> t
      | Lemma k, s -> Lemma k
  end

  (* orderSub (O, s) = O'

       Invariant:
       If   G' |- O order    and    G |- s : G'
       then G |- O' order
       and  G |- O' == O[s] order
    *)
  (* by invariant: no case for All and And *)
  (* normalizeOrder (O) = O'

       Invariant:
       If   G |- O order
       then G |- O' order
       and  G |- O = O' order
       and  each sub term of O' is in normal form.
    *)
  (* by invariant: no case for All and And *)
  (* convOrder (O1, O2) = B'

       Invariant:
       If   G |- O1 order
       and  G |- O2 order
       then B' holds iff G |- O1 == O2 order
    *)
  (* by invariant: no case for All and And *)
  (* decrease T = T'

       Invariant:
       T is either an Assumption or Induction tag
       T' = T - 1
    *)
  (* decrease (Assumption k) = Assumption (k-1)
      | *)
  (* normalizeTag (T, s) = T'

       Invariant:
       If   G |- T : tag
            G' |- s : G
       then G' |- T' = T[s] tag
    *)
  let orderSub = orderSub
  let decrease = decrease
  let splitDepth = splitDepth
  let normalizeOrder = normalizeOrder
  let convOrder = convOrder
  let normalizeTag = normalizeTag
end
(*! sharing Conv.IntSyn = IntSyn' !*)
(* local *)
(* signature STATESYN *)

(* # 1 "src/meta/Statesyn.sml.ml" *)
