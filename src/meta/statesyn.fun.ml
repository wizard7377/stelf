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
end) : STATESYN = struct
  (*! structure IntSyn = IntSyn' !*)
  (*! structure FunSyn = FunSyn' !*)
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

    let rec orderSub = function
      | Arg ((u_, s1), (v_, s2)), s ->
          Arg ((u_, I.comp (s1, s)), (v_, I.comp (s2, s)))
      | Lex os_, s -> Lex (map (function o_ -> orderSub (o_, s)) os_)
      | Simul os_, s -> Simul (map (function o_ -> orderSub (o_, s)) os_)

    let rec normalizeOrder = function
      | Arg (us_, vs_) ->
          Arg ((Whnf.normalize us_, I.id), (Whnf.normalize vs_, I.id))
      | Lex os_ -> Lex (map normalizeOrder os_)
      | Simul os_ -> Simul (map normalizeOrder os_)

    let rec convOrder = function
      | Arg (us1_, _), Arg (us2_, _) -> Conv.conv (us1_, us2_)
      | Lex os1_, Lex os2_ -> convOrders (os1_, os2_)
      | Simul os1_, Simul os2_ -> convOrders (os1_, os2_)

    and convOrders = function
      | [], [] -> true
      | o1_ :: l1_, o2_ :: l2_ -> convOrder (o1_, o2_) && convOrders (l1_, l2_)

    let rec decreaseInfo = function
      | Splits k -> Splits (k - 1)
      | Rl -> Rl
      | RLdone -> RLdone

    let rec decrease = function
      | Lemma sp_ -> Lemma (decreaseInfo sp_)
      | None -> None

    let rec splitDepth (Splits k) = k

    let rec normalizeTag = function
      | (Parameter _ as t_), _ -> T
      | Lemma k_, s -> Lemma k_
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
