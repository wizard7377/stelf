open! Global.Global_
open! Intsyn
open! Intsyn.Lambda_
open! Modes.Modes_

(* # 1 "src/tomega/TomegaAbstract.sig.ml" *)
module Tomega = Lambda_.Tomega

(* Abstraction mechanisms form programs and formulas *)
(* Author: Carsten Schuermann *)
include TOMEGAABSTRACT
(* Signature TOMEGAABSTRACT *)

(* # 1 "src/tomega/TomegaAbstract.fun.ml" *)
open! Basis

exception Error of string

let () =
  Printexc.register_printer (function Error msg -> Some msg | _ -> None)

module TomegaAbstract (TomegaAbstract__0 : sig
  (* Converter from relational representation to a functional
   representation of proof terms *)
  (* Author: Carsten Schuermann *)
  module Global : GLOBAL

  val abstract_raiseType : IntSyn.dctx -> IntSyn.exp -> IntSyn.exp
  val abstract_raiseTerm : IntSyn.dctx -> IntSyn.exp -> IntSyn.exp

  module Whnf : WHNF
  module Subordinate : Subordinate.Subordinate_.SUBORDINATE
end) : TOMEGAABSTRACT = struct
  exception Error = Error

  module Global = TomegaAbstract__0.Global
  module Whnf = TomegaAbstract__0.Whnf
  module Subordinate = TomegaAbstract__0.Subordinate

  open! struct
    module T = Tomega
    module I = IntSyn
    module M = ModeSyn
    module S = Subordinate

    module A = struct
      let raiseType = TomegaAbstract__0.abstract_raiseType
      let raiseTerm = TomegaAbstract__0.abstract_raiseTerm
    end

    let rec shiftCtx (a, t) = match a with
      | I.Null -> (I.Null, t)
      | I.Decl (g, d) ->
          let g', t' = shiftCtx (g, t) in
          (I.Decl (g', I.decSub d t'), I.dot1 t')

    let rec dotn (t, n) = match n with 0 -> t | n -> I.dot1 (dotn (t, n - 1))

    let rec strengthenToSpine = function
      | I.Shift _, 0, (n, s) -> s
      | I.Dot (I.Idx _, t), l, (n, s) ->
          let t' = I.comp t I.invShift in
          strengthenToSpine
            (t', l - 1, (n + 1, I.App (I.Root (I.BVar n, I.Nil), s)))
      | I.Dot (I.Undef, t), l, (n, s) ->
          strengthenToSpine (t, l - 1, (n + 1, s))
      | I.Shift k, l, (n, s) ->
          strengthenToSpine (I.Dot (I.Idx (k + 1), I.Shift (k + 1)), l, (n, s))

    let rec raiseFor a1 b1 = match a1, b1 with
      | b', (T.True, t) -> T.True
      | b', (T.And (f1, f2), t) ->
          let f1' = raiseFor b' (f1, t) in
          let f2' = raiseFor b' (f2, t) in
          T.And (f1', f2')
      | b', (T.Ex ((I.Dec (x, v), q), f), t) ->
          let w = S.weaken b' (I.targetFam v) in
          let iw = Whnf.invert w in
          let b'' = Whnf.strengthen iw b' in
          let v' = A.raiseType b'' (I.EClo (v, I.comp t iw)) in
          let b''', _ = shiftCtx (b', I.shift) in
          let t'' = dotn (I.shift, I.ctxLength b') in
          let t' = I.comp t t'' in
          let s = strengthenToSpine (iw, I.ctxLength b', (1, I.Nil)) in
          let u = I.Root (I.BVar (I.ctxLength b''' + 1), s) in
          let t''' = Whnf.dotEta (I.Exp u) t' in
          let f' = raiseFor b''' (f, t''') in
          T.Ex ((I.Dec (x, v'), q), f')
      | _, (T.All _, _) -> raise Domain

    let rec raisePrg a1 b1 c1 = match a1, b1, c1 with
      | g, (T.Unit, t), _ -> T.Unit
      | g, (T.PairPrg (p1, p2), t), T.And (f1, f2) ->
          let p1' = raisePrg g (p1, t) f1 in
          let p2' = raisePrg g (p2, t) f2 in
          T.PairPrg (p1', p2')
      | g, (T.PairExp (u, p), t), T.Ex ((I.Dec (_, v), _), f) ->
          let w = S.weaken g (I.targetFam v) in
          let iw = Whnf.invert w in
          let g' = Whnf.strengthen iw g in
          let u' = A.raiseTerm g' (I.EClo (u, I.comp t iw)) in
          let p' = raisePrg g (p, t) f in
          T.PairExp (u', p')

    let raiseP g p f =
      let g', s = T.deblockify g in
      let f' = T.forSub f s in
      let p'' = raisePrg g' (p, T.coerceSub s) f' in
      p''

    let raiseF g (f, t) =
      let g', s = T.deblockify g in
      let f' = raiseFor g' (f, I.comp t (T.coerceSub s)) in
      f'
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
  let raisePrg g p f = raisePrg g (p, I.id) f
  let raiseP = raiseP
  let raiseFor = raiseFor
  let raiseF = raiseF
end
(* functor TomegaAbstract *)

(* # 1 "src/tomega/TomegaAbstract.sml.ml" *)
