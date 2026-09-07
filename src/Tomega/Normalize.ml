open! Intsyn
open! Intsyn.Lambda_

(* # 1 "src/tomega/Normalize.sig.ml" *)
module Tomega = Lambda_.Tomega

(* Normalizer for Delphin meta level *)
(* Author: Carsten Schuermann *)
include NORMALIZE

(* # 1 "src/tomega/Normalize.fun.ml" *)
open! Basis

exception Error of string

let () =
  Printexc.register_printer (function Error msg -> Some msg | _ -> None)

module Normalize (Normalize__0 : sig
  (* Internal syntax for functional proof term calculus *)
  (* Author: Carsten Schuermann *)
  module Whnf : WHNF
end) : NORMALIZE = struct
  module IntSyn = IntSyn
  module Tomega = Tomega

  exception Error = Error

  open! struct
    module Whnf = Normalize__0.Whnf
    module I = IntSyn
    module T = Tomega

    let rec normalizeFor a1 b1 = match a1, b1 with
      | T.All ((d, q), f), t ->
          T.All ((T.decSub d t, q), normalizeFor f (T.dot1 t))
      | T.Ex ((d, q), f), t ->
          T.Ex ((I.decSub d (T.coerceSub t), q), normalizeFor f (T.dot1 t))
      | T.And (f1, f2), t ->
          T.And (normalizeFor f1 t, normalizeFor f2 t)
      | T.FClo (f, t1), t2 -> normalizeFor f (T.comp t1 t2)
      | T.World (w, f), t -> T.World (w, normalizeFor f t)
      | T.True, _ -> T.True

    let rec normalizePrg a1 b1 = match a1, b1 with
      | (T.Const _ as p), t -> p
      | (T.Var n as p), t -> normalizePrg p (T.Dot (T.varSub n t, T.id))
      | T.Lam (d, p'), t -> T.Lam (d, normalizePrg p' (T.dot1 t))
      | T.PairExp (u, p'), t ->
          let u', s' = Whnf.whnf ((u, T.coerceSub t) : I.eclo) in
          T.PairExp (I.EClo (u', s'), normalizePrg p' t)
      | T.PairPrg (p1, p2), t ->
          T.PairPrg (normalizePrg p1 t, normalizePrg p2 t)
      | T.Unit, _ -> T.Unit
      | T.Redex (p, s), t -> T.Redex (normalizePrg p t, normalizeSpine s)
      | T.Rec (d, p), t -> T.Rec (d, normalizePrg p t)
      | (T.Case _ as p), t -> p
      | (T.EVar (psi, { contents = Some p' }, _, _, _, _) as p), t ->
          normalizePrg p' t

    and normalizeSpine = function
      | T.Nil -> T.Nil
      | T.AppExp (u, s) -> T.AppExp (u, normalizeSpine s)
      | T.AppPrg (p, s) ->
          T.AppPrg (normalizePrg p T.id, normalizeSpine s)
      | T.AppBlock (b, s) -> T.AppBlock (b, normalizeSpine s)

    let rec normalizeSub = function
      | T.Shift n as s -> s
      | T.Dot (T.Prg p, s) ->
          T.Dot (T.Prg (normalizePrg p T.id), normalizeSub s)
      | T.Dot (f, s) -> T.Dot (f, normalizeSub s)
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
  let normalizeSpine s _t = normalizeSpine s
  let normalizeSub = normalizeSub
end

(* # 1 "src/tomega/Normalize.sml.ml" *)
