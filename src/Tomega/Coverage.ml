open! Basis
open! Global
open! Global.Global_
open! Intsyn
open! Intsyn.Lambda_
open! Worldcheck
open! Worldcheck.Worldcheck_
open! Cover
open! Cover.Cover_
open! Formatter
open! Formatter__Formatter_
open! Names
open! Names.Names_
open! Print
open! Print.Print_
open! Typecheck
open! Typecheck.Typecheck_
open! Subordinate
open! Subordinate
open! Meta
open! Meta.Meta_
open! Modes
open! Modes.Modes_
open! Trail
open! Trail.Trail_

(* # 1 "src/tomega/Coverage.sig.ml" *)
open! Basis
module Tomega = Lambda_.Tomega

(* Unification on Formulas *)
(* Author: Carsten Schuermann *)
include COVERAGE
(* Signature TOMEGACOVERAGE *)

(* # 1 "src/tomega/Coverage.fun.ml" *)
open! Basis

exception Error of string

let () =
  Printexc.register_printer (function Error msg -> Some msg | _ -> None)

module MakeTomegaCoverage
    (TomegaPrint : Tomegaprint.TOMEGAPRINT)
    (TomegaTypeCheck : TOMEGATYPECHECK.TOMEGATYPECHECK)
    (Cover : COVER) : TOMEGACOVERAGE = struct
  (*
  (* Coverage checker for programs *)
  (* Author: Carsten Schuermann *)
  (*! structure IntSyn' : INTSYN !*)
  (*! structure Tomega' : TOMEGA !*)
  (*! sharing Tomega'.IntSyn = IntSyn' !*)
  module TomegaPrint : Tomegaprint.TOMEGAPRINT

  (*! sharing TomegaPrint.IntSyn = IntSyn' !*)
  (*! sharing TomegaPrint.Tomega = Tomega' !*)
  module TomegaTypeCheck : TOMEGATYPECHECK.TOMEGATYPECHECK

  (*! sharing TomegaTypeCheck.IntSyn = IntSyn' !*)
  (*! sharing TomegaTypeCheck.Tomega = Tomega' !*)
  module Cover : COVER
*)
  (*! structure IntSyn = IntSyn' !*)
  (*! structure Tomega = Tomega' !*)
  exception Error = Error

  open! struct
    module I = IntSyn
    module T = Tomega
    module Cover = Cover
    module TomegaTypeCheck = TomegaTypeCheck

    let chatter chlev f = Display.chatter_s chlev ("[coverage] " ^ f ())

    let rec purifyFor = function
      | (T.Unit, t), (psi, T.True), s -> (t, psi, s)
      | (T.PairExp (u_, p_), t), (psi, T.Ex ((d_, _), f_)), s ->
          purifyFor
            ( (p_, T.Dot (T.Exp u_, t)),
              (I.Decl (psi, T.UDec d_), f_),
              T.comp s T.shift )

    let rec purifyCtx = function
      | (T.Shift k as t), psi -> (t, psi, T.id)
      | T.Dot (T.Prg p_, t), I.Decl (psi, T.PDec (_, T.All _, _, _)) ->
          let t', psi', s' = purifyCtx (t, psi) in
          (t', psi', T.Dot (T.Undef, s'))
      | T.Dot (T.Prg (T.Var _), t), I.Decl (psi, T.PDec (_, _, _, _)) ->
          let t', psi', s' = purifyCtx (t, psi) in
          (t', psi', T.Dot (T.Undef, s'))
      | T.Dot (T.Prg (T.Const _), t), I.Decl (psi, T.PDec (_, _, _, _)) ->
          let t', psi', s' = purifyCtx (t, psi) in
          (t', psi', T.Dot (T.Undef, s'))
      | T.Dot (T.Prg (T.PairPrg (_, _)), t), I.Decl (psi, T.PDec (_, _, _, _))
        ->
          let t', psi', s' = purifyCtx (t, psi) in
          (t', psi', T.Dot (T.Undef, s'))
      | T.Dot (T.Prg p_, t), I.Decl (psi, T.PDec (_, f_, _, _)) ->
          let t', psi', s' = purifyCtx (t, psi) in
          let t'', psi'', s'' =
            purifyFor ((p_, t'), (psi', T.forSub f_ s'), s')
          in
          (t'', psi'', T.Dot (T.Undef, s''))
      | T.Dot (f_, t), I.Decl (psi, T.UDec d_) ->
          let t', psi', s' = purifyCtx (t, psi) in
          ( T.Dot (f_, t'),
            I.Decl (psi', T.UDec (I.decSub d_ (T.coerceSub s'))),
            T.dot1 s' )

    let purify (psi0, t, psi) =
      let t', psi', s' = purifyCtx (t, psi) in
      ignore (TomegaTypeCheck.checkSub psi0 t' psi');
      (psi0, t', psi')

    let rec coverageCheckPrg a b c = match a, b, c with
      | w_, psi, T.Lam (d_, p_) -> coverageCheckPrg w_ (I.Decl (psi, d_)) p_
      | w_, psi, T.New p_ -> coverageCheckPrg w_ psi p_
      | w_, psi, T.PairExp (u_, p_) -> coverageCheckPrg w_ psi p_
      | w_, psi, T.PairBlock (b_, p_) -> coverageCheckPrg w_ psi p_
      | w_, psi, T.PairPrg (p1_, p2_) -> begin
          coverageCheckPrg w_ psi p1_;
          coverageCheckPrg w_ psi p2_
        end
      | w_, psi, Unit -> ()
      | w_, psi, T.Var _ -> ()
      | w_, psi, T.Const _ -> ()
      | w_, psi, T.Rec (d_, p_) -> coverageCheckPrg w_ (I.Decl (psi, d_)) p_
      | w_, psi, T.Case (T.Cases omega_) ->
          coverageCheckCases (w_, psi, omega_, [])
      | w_, psi, (T.Let (d_, p1_, p2_) as p_) -> begin
          coverageCheckPrg w_ psi p1_;
          coverageCheckPrg w_ (I.Decl (psi, d_)) p2_
        end
      | w_, psi, T.Redex (p_, s_) -> coverageCheckSpine (w_, psi, s_)

    and coverageCheckSpine = function
      | w_, psi, T.Nil -> ()
      | w_, psi, T.AppExp (u_, s_) -> coverageCheckSpine (w_, psi, s_)
      | w_, psi, T.AppBlock (b_, s_) -> coverageCheckSpine (w_, psi, s_)
      | w_, psi, T.AppPrg (p_, s_) -> begin
          coverageCheckPrg w_ psi p_;
          coverageCheckSpine (w_, psi, s_)
        end

    and coverageCheckCases = function
      | w_, psi, [], [] -> ()
      | w_, psi, [], cs_ ->
          let _ =
            chatter 5 (function () ->
                Int.toString (List.length cs_) ^ " cases to be checked\n")
          in
          let ((_, _, psi') :: _ as cs'_) = map purify cs_ in
          let cs''_ =
            map
              (function psi0, t, _ -> (T.coerceCtx psi0, T.coerceSub t))
              cs'_
          in
          Cover.coverageCheckCases w_ cs''_ (T.coerceCtx psi')
      | w_, psi, (psi', t, p_) :: omega_, cs_ -> begin
          coverageCheckPrg w_ psi' p_;
          coverageCheckCases (w_, psi, omega_, (psi', t, psi) :: cs_)
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
