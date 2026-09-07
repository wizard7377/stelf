open! Intsyn
open! Intsyn.Lambda_
open! Cover.Cover_

(* # 1 "src/tomega/Coverage.sig.ml" *)
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

    let rec purifyFor (a, b, s) = match a, b with
      | (T.Unit, t), (psi, T.True) -> (t, psi, s)
      | (T.PairExp (u, p), t), (psi, T.Ex ((d, _), f)) ->
          purifyFor
            ( (p, T.Dot (T.Exp u, t)),
              (I.Decl (psi, T.UDec d), f),
              T.comp s T.shift )

    let rec purifyCtx = function
      | (T.Shift k as t), psi -> (t, psi, T.id)
      | T.Dot (T.Prg p, t), I.Decl (psi, T.PDec (_, T.All _, _, _)) ->
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
      | T.Dot (T.Prg p, t), I.Decl (psi, T.PDec (_, f, _, _)) ->
          let t', psi', s' = purifyCtx (t, psi) in
          let t'', psi'', s'' =
            purifyFor ((p, t'), (psi', T.forSub f s'), s')
          in
          (t'', psi'', T.Dot (T.Undef, s''))
      | T.Dot (f, t), I.Decl (psi, T.UDec d) ->
          let t', psi', s' = purifyCtx (t, psi) in
          ( T.Dot (f, t'),
            I.Decl (psi', T.UDec (I.decSub d (T.coerceSub s'))),
            T.dot1 s' )

    let purify (psi0, t, psi) =
      let t', psi', s' = purifyCtx (t, psi) in
      ignore (TomegaTypeCheck.checkSub psi0 t' psi');
      (psi0, t', psi')

    let rec coverageCheckPrg a b c = match a, b, c with
      | w, psi, T.Lam (d, p) -> coverageCheckPrg w (I.Decl (psi, d)) p
      | w, psi, T.New p -> coverageCheckPrg w psi p
      | w, psi, T.PairExp (u, p) -> coverageCheckPrg w psi p
      | w, psi, T.PairBlock (b, p) -> coverageCheckPrg w psi p
      | w, psi, T.PairPrg (p1, p2) -> begin
          coverageCheckPrg w psi p1;
          coverageCheckPrg w psi p2
        end
      | w, psi, Unit -> ()
      | w, psi, T.Var _ -> ()
      | w, psi, T.Const _ -> ()
      | w, psi, T.Rec (d, p) -> coverageCheckPrg w (I.Decl (psi, d)) p
      | w, psi, T.Case (T.Cases omega) ->
          coverageCheckCases (w, psi, omega, [])
      | w, psi, (T.Let (d, p1, p2) as p) -> begin
          coverageCheckPrg w psi p1;
          coverageCheckPrg w (I.Decl (psi, d)) p2
        end
      | w, psi, T.Redex (p, s) -> coverageCheckSpine (w, psi, s)

    and coverageCheckSpine (w, psi, a) = match a with
      | T.Nil -> ()
      | T.AppExp (u, s) -> coverageCheckSpine (w, psi, s)
      | T.AppBlock (b, s) -> coverageCheckSpine (w, psi, s)
      | T.AppPrg (p, s) -> begin
          coverageCheckPrg w psi p;
          coverageCheckSpine (w, psi, s)
        end

    and coverageCheckCases (w, psi, a, cs) = match a, cs with
      | [], [] -> ()
      | [], cs ->
          ignore (chatter 5 (function () ->
                Int.toString (List.length cs) ^ " cases to be checked\n"));
          let ((_, _, psi') :: _ as cs') = map purify cs in
          let cs'' =
            map
              (function psi0, t, _ -> (T.coerceCtx psi0, T.coerceSub t))
              cs'
          in
          Cover.coverageCheckCases w cs'' (T.coerceCtx psi')
      | (psi', t, p) :: omega, cs -> begin
          coverageCheckPrg w psi' p;
          coverageCheckCases (w, psi, omega, (psi', t, psi) :: cs)
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
