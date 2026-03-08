open! Basis

module TomegaAbstract (TomegaAbstract__0 : sig
  (* Converter from relational representation to a functional
   representation of proof terms *)
  (* Author: Carsten Schuermann *)
  module Global : GLOBAL
  module Abstract : ABSTRACT
  module Whnf : WHNF
  module Subordinate : SUBORDINATE
end) : TOMEGAABSTRACT = struct
  exception Error of string

  open! struct
    module T = Tomega
    module I = IntSyn
    module M = ModeSyn
    module S = Subordinate
    module A = Abstract

    let rec shiftCtx = function
      | null_, t -> (I.null_, t)
      | I.Decl (g_, d_), t ->
          let g'_, t' = shiftCtx (g_, t) in
          (I.Decl (g'_, I.decSub (d_, t')), I.dot1 t')

    let rec dotn = function t, 0 -> t | t, n -> I.dot1 (dotn (t, n - 1))

    let rec strengthenToSpine = function
      | I.Shift _, 0, (n, s_) -> s_
      | I.Dot (I.Idx _, t), l, (n, s_) ->
          let t' = I.comp (t, I.invShift) in
          strengthenToSpine
            (t', l - 1, (n + 1, I.App (I.Root (I.BVar n, I.nil_), s_)))
      | I.Dot (undef_, t), l, (n, s_) ->
          strengthenToSpine (t, l - 1, (n + 1, s_))
      | I.Shift k, l, (n, s_) ->
          strengthenToSpine (I.Dot (I.Idx (k + 1), I.Shift (k + 1)), l, (n, s_))

    let rec raiseFor = function
      | b'_, (true_, t) -> T.true_
      | b'_, (T.And (f1_, f2_), t) ->
          let f1'_ = raiseFor (b'_, (f1_, t)) in
          let f2'_ = raiseFor (b'_, (f2_, t)) in
          T.And (f1'_, f2'_)
      | b'_, (T.Ex ((I.Dec (x, v_), q_), f_), t) ->
          let w = S.weaken (b'_, I.targetFam v_) in
          let iw = Whnf.invert w in
          let b''_ = Whnf.strengthen (iw, b'_) in
          let v'_ = A.raiseType (b''_, I.EClo (v_, I.comp (t, iw))) in
          let b'''_, _ = shiftCtx (b'_, I.shift) in
          let t'' = dotn (I.shift, I.ctxLength b'_) in
          let t' = I.comp (t, t'') in
          let s_ = strengthenToSpine (iw, I.ctxLength b'_, (1, I.nil_)) in
          let u_ = I.Root (I.BVar (I.ctxLength b'''_ + 1), s_) in
          let t''' = Whnf.dotEta (I.Exp u_, t') in
          let f'_ = raiseFor (b'''_, (f_, t''')) in
          T.Ex ((I.Dec (x, v'_), q_), f'_)
      | _, (T.All _, _) -> raise Domain

    let rec raisePrg = function
      | g_, (unit_, t), _ -> T.unit_
      | g_, (T.PairPrg (p1_, p2_), t), T.And (f1_, f2_) ->
          let p1'_ = raisePrg (g_, (p1_, t), f1_) in
          let p2'_ = raisePrg (g_, (p2_, t), f2_) in
          T.PairPrg (p1'_, p2'_)
      | g_, (T.PairExp (u_, p_), t), T.Ex ((I.Dec (_, v_), _), f_) ->
          let w = S.weaken (g_, I.targetFam v_) in
          let iw = Whnf.invert w in
          let g'_ = Whnf.strengthen (iw, g_) in
          let u'_ = A.raiseTerm (g'_, I.EClo (u_, I.comp (t, iw))) in
          let p'_ = raisePrg (g_, (p_, t), f_) in
          T.PairExp (u'_, p'_)

    let rec raiseP (g_, p_, f_) =
      let g'_, s = T.deblockify g_ in
      let f'_ = T.forSub (f_, s) in
      let p''_ = raisePrg (g'_, (p_, T.coerceSub s), f'_) in
      p''_

    let rec raiseF (g_, (f_, t)) =
      let g'_, s = T.deblockify g_ in
      let f'_ = raiseFor (g'_, (f_, I.comp (t, T.coerceSub s))) in
      f'_
  end

  (* dotn (t, n) = t'

       Invariant:
       If   Psi0 |- t : Psi
       and  |G| = n   for any G
       then Psi0, G[t] |- t : Psi, G
    *)
  (* =0 *)
  (* = 1 *)
  (* raiseFor (B, (F, t)) = (P', F'))

       Invariant:
       If   Psi, B, G |-  F for
       and  Psi, G', B' |- t : Psi, B, G
       then Psi, G' |-  F' for
       and  F' = raise (B', F[t])   (using subordination)
    *)
  (* Psi, G', B' |- V[t] : type *)
  (* Psi, B, G, x:V |- F for *)
  (* Psi, G' |- B' ctx  *)
  (*        val (w, S) = subweaken (B', 1, I.targetFam V, I.Nil)     *)
  (* B'  |- w  : B''    *)
  (* B'' |- iw : B'     *)
  (* Psi0, G' |- B'' ctx *)
  (* Psi0, G' |- V' : type *)
  (* Psi, G', x: V' |- B''' ctx *)
  (* Psi, G', x: V', B''' |- t'' :   Psi, G', B' *)
  (* Psi, G', B' |- t : Psi, B, G  *)
  (* Psi, G', x:V', B''' |- t' : Psi, B, G *)
  (* Psi, G', x:V', B''' |- w : Psi,G', x:V', B'''' *)
  (* Psi, G', x:V', B''' |- S : V' [^|B'''|] >> type  *)
  (* Psi, G', x:V', B''' |- U : V[t'] *)
  (* Psi, G', x:V', B''' |- t''' :  Psi, B, G, x:V *)
  (* Psi, G', x:V' |- F' for*)
  (* Psi, G', x:V', B''' |- t''' :  Psi, B, G, x:V *)
  (* raisePrg (G, P, F) = (P', F'))

       Invariant:
       If   Psi, G |- P in F
       and  Psi |- G : blockctx
       then Psi |- P' in F'
       and  P = raise (G, P')   (using subordination)
       and  F = raise (G, F')   (using subordination)
    *)
  (* G  |- w  : G'    *)
  (* G' |- iw : G     *)
  (* Psi0, G' |- B'' ctx *)
  (*      val P' = T.normalizePrg (P, s)  G' |- P' : F'  *)
  let raisePrg = function g_, p_, f_ -> raisePrg (g_, (p_, I.id), f_)
  let raiseP = raiseP
  let raiseFor = raiseFor
  let raiseF = raiseF
end
(* functor TomegaAbstract *)
