(* # 1 "src/tomega/Coverage.sig.ml" *)
open! Basis
module Tomega = Lambda_.Tomega

(* Unification on Formulas *)
(* Author: Carsten Schuermann *)
include Coverage_intf
(* Signature TOMEGACOVERAGE *)

(* # 1 "src/tomega/Coverage.fun.ml" *)
open! Basis

module MakeTomegaCoverage
    (TomegaPrint : Tomegaprint.TOMEGAPRINT)
    (TomegaTypeCheck : TomegaTypecheck_intf.TOMEGATYPECHECK)
    (Cover : COVER) :
  TOMEGACOVERAGE =
struct
(*
  (* Coverage checker for programs *)
  (* Author: Carsten Schuermann *)
  (*! structure IntSyn' : INTSYN !*)
  (*! structure Tomega' : TOMEGA !*)
  (*! sharing Tomega'.IntSyn = IntSyn' !*)
  module TomegaPrint : Tomegaprint.TOMEGAPRINT

  (*! sharing TomegaPrint.IntSyn = IntSyn' !*)
  (*! sharing TomegaPrint.Tomega = Tomega' !*)
  module TomegaTypeCheck : TomegaTypecheck_intf.TOMEGATYPECHECK

  (*! sharing TomegaTypeCheck.IntSyn = IntSyn' !*)
  (*! sharing TomegaTypeCheck.Tomega = Tomega' !*)
  module Cover : COVER
*)
  (*! structure IntSyn = IntSyn' !*)
  (*! structure Tomega = Tomega' !*)
  exception Error of string

  open! struct
    module I = IntSyn
    module T = Tomega
    module Cover = Cover
    module TomegaTypeCheck = TomegaTypeCheck

    let rec chatter chlev f =
      begin if !Global.chatter >= chlev then print ("[coverage] " ^ f ())
      else ()
      end

    let rec purifyFor = function
      | (T.Unit, t), (psi_, T.True), s -> (t, psi_, s)
      | (T.PairExp (u_, p_), t), (psi_, T.Ex ((d_, _), f_)), s ->
          purifyFor
            ( (p_, T.Dot (T.Exp u_, t)),
              (I.Decl (psi_, T.UDec d_), f_),
              T.comp (s, T.shift) )

    let rec purifyCtx = function
      | (T.Shift k as t), psi_ -> (t, psi_, T.id)
      | T.Dot (T.Prg p_, t), I.Decl (psi_, T.PDec (_, T.All _, _, _)) ->
          let t', psi'_, s' = purifyCtx (t, psi_) in
          (t', psi'_, T.Dot (T.Undef, s'))
      | T.Dot (T.Prg (T.Var _), t), I.Decl (psi_, T.PDec (_, _, _, _)) ->
          let t', psi'_, s' = purifyCtx (t, psi_) in
          (t', psi'_, T.Dot (T.Undef, s'))
      | T.Dot (T.Prg (T.Const _), t), I.Decl (psi_, T.PDec (_, _, _, _)) ->
          let t', psi'_, s' = purifyCtx (t, psi_) in
          (t', psi'_, T.Dot (T.Undef, s'))
      | T.Dot (T.Prg (T.PairPrg (_, _)), t), I.Decl (psi_, T.PDec (_, _, _, _))
        ->
          let t', psi'_, s' = purifyCtx (t, psi_) in
          (t', psi'_, T.Dot (T.Undef, s'))
      | T.Dot (T.Prg p_, t), I.Decl (psi_, T.PDec (_, f_, _, _)) ->
          let t', psi'_, s' = purifyCtx (t, psi_) in
          let t'', psi''_, s'' =
            purifyFor ((p_, t'), (psi'_, T.forSub (f_, s')), s')
          in
          (t'', psi''_, T.Dot (T.Undef, s''))
      | T.Dot (f_, t), I.Decl (psi_, T.UDec d_) ->
          let t', psi'_, s' = purifyCtx (t, psi_) in
          ( T.Dot (f_, t'),
            I.Decl (psi'_, T.UDec (I.decSub (d_, T.coerceSub s'))),
            T.dot1 s' )

    let rec purify (psi0_, t, psi_) =
      let t', psi'_, s' = purifyCtx (t, psi_) in
      let _ = TomegaTypeCheck.checkSub (psi0_, t', psi'_) in
      (psi0_, t', psi'_)

    let rec coverageCheckPrg = function
      | w_, psi_, T.Lam (d_, p_) -> coverageCheckPrg (w_, I.Decl (psi_, d_), p_)
      | w_, psi_, T.New p_ -> coverageCheckPrg (w_, psi_, p_)
      | w_, psi_, T.PairExp (u_, p_) -> coverageCheckPrg (w_, psi_, p_)
      | w_, psi_, T.PairBlock (b_, p_) -> coverageCheckPrg (w_, psi_, p_)
      | w_, psi_, T.PairPrg (p1_, p2_) -> begin
          coverageCheckPrg (w_, psi_, p1_);
          coverageCheckPrg (w_, psi_, p2_)
        end
      | w_, psi_, Unit -> ()
      | w_, psi_, T.Var _ -> ()
      | w_, psi_, T.Const _ -> ()
      | w_, psi_, T.Rec (d_, p_) -> coverageCheckPrg (w_, I.Decl (psi_, d_), p_)
      | w_, psi_, T.Case (T.Cases omega_) ->
          coverageCheckCases (w_, psi_, omega_, [])
      | w_, psi_, (T.Let (d_, p1_, p2_) as p_) -> begin
          coverageCheckPrg (w_, psi_, p1_);
          coverageCheckPrg (w_, I.Decl (psi_, d_), p2_)
        end
      | w_, psi_, T.Redex (p_, s_) -> coverageCheckSpine (w_, psi_, s_)

    and coverageCheckSpine = function
      | w_, psi_, T.Nil -> ()
      | w_, psi_, T.AppExp (u_, s_) -> coverageCheckSpine (w_, psi_, s_)
      | w_, psi_, T.AppBlock (b_, s_) -> coverageCheckSpine (w_, psi_, s_)
      | w_, psi_, T.AppPrg (p_, s_) -> begin
          coverageCheckPrg (w_, psi_, p_);
          coverageCheckSpine (w_, psi_, s_)
        end

    and coverageCheckCases = function
      | w_, psi_, [], [] -> ()
      | w_, psi_, [], cs_ ->
          let _ =
            chatter 5 (function () ->
                Int.toString (List.length cs_) ^ " cases to be checked\n")
          in
          let ((_, _, psi'_) :: _ as cs'_) = map purify cs_ in
          let cs''_ =
            map
              (function psi0_, t, _ -> (T.coerceCtx psi0_, T.coerceSub t))
              cs'_
          in
          Cover.coverageCheckCases (w_, cs''_, T.coerceCtx psi'_)
      | w_, psi_, (psi'_, t, p_) :: omega_, cs_ -> begin
          coverageCheckPrg (w_, psi'_, p_);
          coverageCheckCases (w_, psi_, omega_, (psi'_, t, psi_) :: cs_)
        end
  end

  (* chatter chlev f = ()

       Invariant:
       f () returns the string to be printed
         if current chatter level exceeds chlev
    *)
  (* purifyFor ((P, t), (Psi, F), s) = (t', Psi', s')

       Invariant:
       If    Psi0 |- t : Psi
       and   Psi0 |- P in F[t]
       and   Psi |- s : Psi1
       and   P == <M1, <M2, ... Mn, <>>>>
       and   F[t] = Ex x1:A1 ... Ex xn:An.true
       then  Psi' = Psi, x::A1, .... An
       and   t' = Mn...M1.t
       then  Psi0 |- t' : Psi'
       and   Psi' |- s' : Psi1
    *)
  (*      | purifyFor ((T.Lam _, _), (_, _), _) = raise Domain
      | purifyFor ((T.New _, _), (_,  _), _) = raise Domain
      | purifyFor ((T.PairBlock _, _), (_,  _), _) = raise Domain
      | purifyFor ((T.PairPrg _, _), (_,  _), _) = raise Domain
      | purifyFor ((T.Unit, _), (_,  _), _) = raise Domain
      | purifyFor ((T.Root (T.Var k, _), _), (_,  _), _) = raise Domain
      | purifyFor ((T.Redex _, _), (_,  _), _) = raise Domain
      | purifyFor ((T.Rec _, _), (_,  _), _) = raise Domain
      | purifyFor ((T.Case _, _), (_,  _), _) = raise Domain
      | purifyFor ((T.PClo _, _), (_,  _), _) = raise Domain
      | purifyFor ((T.Let _, _), (_,  _), _) = raise Domain
      | purifyFor ((T.EVar _, _), (_,  _), _) = raise Domain
*)
  (*  | purifyFor (Psi, T.All (_, F), s) = (Psi, s)
        cannot occur by invariant Mon Dec  2 18:03:20 2002 -cs *)
  (* purifyCtx (t, Psi) = (t', Psi', s')
       If    Psi0 |- t : Psi
       then  Psi0 |- t' : Psi'
       and   Psi' |- s' : Psi
    *)
  (* Mutual recursive predicates
                                           don't have to be checked.
                                         --cs Fri Jan  3 11:35:09 2003 *)
  (* subToSpine (Psi', t, Psi) *)
  let coverageCheckPrg = coverageCheckPrg
end
(*! sharing Cover.IntSyn = IntSyn' !*)
(*! sharing Cover.Tomega = Tomega' !*)
(* chatter 5 (""fn () => TomegaPrint.prgToString (Psi, P)); *)
(*    | coverageCheckPrg (Psi, T.EVar) =
          should not occur by invariant  *)
(*    | coverageCheckSpine (Psi, T.SClo _) =
          should not occur by invariant  *)

(* # 1 "src/tomega/Coverage.sml.ml" *)
