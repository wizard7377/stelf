(* # 1 "src/tomega/Normalize.sig.ml" *)
open! Basis
module Tomega = Lambda_.Tomega

(* Normalizer for Delphin meta level *)
(* Author: Carsten Schuermann *)
include Normalize_intf
(* # 1 "src/tomega/Normalize.fun.ml" *)
open! Basis

module Normalize (Normalize__0 : sig
  (* Internal syntax for functional proof term calculus *)
  (* Author: Carsten Schuermann *)
  module Whnf : WHNF
end) : NORMALIZE = struct
  module IntSyn = IntSyn
  module Tomega = Tomega

  exception Error of string

  open! struct
    module Whnf = Normalize__0.Whnf
    module I = IntSyn
    module T = Tomega

    let rec normalizeFor = function
      | T.All ((d_, q_), f_), t ->
          T.All ((T.decSub (d_, t), q_), normalizeFor (f_, T.dot1 t))
      | T.Ex ((d_, q_), f_), t ->
          T.Ex ((I.decSub (d_, T.coerceSub t), q_), normalizeFor (f_, T.dot1 t))
      | T.And (f1_, f2_), t ->
          T.And (normalizeFor (f1_, t), normalizeFor (f2_, t))
      | T.FClo (f_, t1), t2 -> normalizeFor (f_, T.comp (t1, t2))
      | T.World (w_, f_), t -> T.World (w_, normalizeFor (f_, t))
      | T.True, _ -> T.True

    let rec normalizePrg = function
      | (T.Const _ as p_), t -> p_
      | (T.Var n as p_), t -> normalizePrg (p_, T.Dot (T.varSub (n, t), T.id))
      | T.Lam (d_, p'_), t -> T.Lam (d_, normalizePrg (p'_, T.dot1 t))
      | T.PairExp (u_, p'_), t ->
          let u'_, s'_ = Whnf.whnf ((u_, T.coerceSub t) : I.eclo) in
          T.PairExp (I.EClo (u'_, s'_), normalizePrg (p'_, t))
      | T.PairPrg (p1_, p2_), t ->
          T.PairPrg (normalizePrg (p1_, t), normalizePrg (p2_, t))
      | T.Unit, _ -> T.Unit
      | T.Redex (p_, s_), t -> T.Redex (normalizePrg (p_, t), normalizeSpine s_)
      | T.Rec (d_, p_), t -> T.Rec (d_, normalizePrg (p_, t))
      | (T.Case _ as p_), t -> p_
      | (T.EVar (psi_, { contents = Some p'_ }, _, _, _, _) as p_), t ->
          normalizePrg (p'_, t)

    and normalizeSpine = function
      | T.Nil -> T.Nil
      | T.AppExp (u_, s_) -> T.AppExp (u_, normalizeSpine s_)
      | T.AppPrg (p_, s_) ->
          T.AppPrg (normalizePrg (p_, T.id), normalizeSpine s_)
      | T.AppBlock (b_, s_) -> T.AppBlock (b_, normalizeSpine s_)

    let rec normalizeSub = function
      | T.Shift n as s -> s
      | T.Dot (T.Prg p_, s) ->
          T.Dot (T.Prg (normalizePrg (p_, T.id)), normalizeSub s)
      | T.Dot (f_, s) -> T.Dot (f_, normalizeSub s)
  end

  (*      | normalizeFor (T.FVar (G, r))   think about it *)
  (* normalizePrg (P, t) = (P', t')

       Invariant:
       If   Psi' |- P :: F
       and  Psi  |- t :: Psi'
       and  P doesn't contain free EVars
       then there exists a Psi'', F'
       s.t. Psi'' |- F' for
       and  Psi'' |- P' :: F'
       and  Psi |- t' : Psi''
       and  Psi |- F [t] == F' [t']
       and  Psi |- P [t] == P' [t'] : F [t]
       and  Psi |- P' [t'] :nf: F [t]
    *)
  (*      | normalizePrg (T.PairBlock (B, P'), t) =
          T.PairBlock (B, normalizePrg P') *)
  (* Clearly, the redex should be removed here *)
  (*
    and normalizeDec (T.UDec D, t) = T.UDec (I.decSub (D, T.coerceSub t))
      | normalizeDec (T.BDec (k, t1), t2) = 
      | normalizeDec (T.PDec (n, F), t) = T.PDec (n, (normalizeFor (F, t)))
*)
  let normalizeFor = normalizeFor
  let normalizePrg = normalizePrg
  let normalizeSpine (s_, _t) = normalizeSpine s_
  let normalizeSub = normalizeSub
end

(* # 1 "src/tomega/Normalize.sml.ml" *)
