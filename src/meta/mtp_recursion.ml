(* # 1 "src/meta/recursion.sig.ml" *)
open! Basis
open Funsyn
open Statesyn
open Mtp_global
open Mtp_abstract
open Mtp_print
open Funtypecheck
open Funprint

(* Recursion: Version 1.3 *)
(* Author: Carsten Schuermann *)
module type MTPRECURSION = sig
  module StateSyn : STATESYN

  exception Error of string

  type nonrec operator

  val expand : StateSyn.state -> operator
  val apply : operator -> StateSyn.state
  val menu : operator -> string
end
(* signature MTPRECURSION *)

(* # 1 "src/meta/recursion.fun.ml" *)
open! Global
open! Abstract
open! Basis

(* Meta Recursion Version 1.3 *)
(* Author: Carsten Schuermann *)
(* See [Rohwedder,Pfenning ESOP'96] *)
module MTPRecursion (MTPRecursion__0 : sig
  module MTPGlobal : MTPGLOBAL
  module Global : GLOBAL

  (*! structure IntSyn : INTSYN !*)
  (*! structure FunSyn : FUNSYN !*)
  (*! sharing FunSyn.IntSyn = IntSyn !*)
  module StateSyn' : STATESYN

  (*! sharing StateSyn'.IntSyn = IntSyn !*)
  (*! sharing StateSyn'.FunSyn = FunSyn !*)
  module Abstract : ABSTRACT

  (*! sharing Abstract.IntSyn = IntSyn !*)
  module MTPAbstract : MTPABSTRACT

  (*! sharing MTPAbstract.IntSyn = IntSyn !*)
  (*! sharing MTPAbstract.FunSyn = FunSyn !*)
  module FunTypeCheck : FUNTYPECHECK

  (*! sharing FunTypeCheck.FunSyn = FunSyn !*)
  module MTPrint : MTPRINT
  module Whnf : WHNF

  (*! sharing Whnf.IntSyn = IntSyn !*)
  module Unify : UNIFY

  (*! sharing Unify.IntSyn = IntSyn !*)
  module Conv : CONV

  (*! sharing Conv.IntSyn = IntSyn !*)
  module Names : NAMES

  (*! sharing Names.IntSyn = IntSyn !*)
  module Subordinate : SUBORDINATE

  (*! sharing Subordinate.IntSyn = IntSyn !*)
  module Print : PRINT

  (*! sharing Print.IntSyn = IntSyn !*)
  module TypeCheck : TYPECHECK

  (*! sharing TypeCheck.IntSyn = IntSyn !*)
  module Formatter : FORMATTER
  module FunPrint : FUNPRINT
end) : MTPRECURSION = struct
  open MTPRecursion__0
  module StateSyn = StateSyn'

  exception Error of string

  type nonrec operator = StateSyn.state

  open! struct
    module I = IntSyn
    module F = FunSyn
    module S = StateSyn
    module N = Names
    module Fmt = Formatter
    module A = MTPAbstract

    type dec = Lemma of int * F.for_

    let rec closedCtx = function
      | I.Null -> ()
      | I.Decl (g_, d_) -> begin
          if Abstract.closedDec (g_, (d_, I.id)) then raise Domain
          else closedCtx g_
        end

    let rec spine = function
      | 0 -> I.Nil
      | n -> I.App (I.Root (I.BVar n, I.Nil), spine (n - 1))

    let rec someEVars = function
      | g_, [], s -> s
      | g_, I.Dec (_, v_) :: l_, s ->
          someEVars (g_, l_, I.Dot (I.Exp (I.newEVar (g_, I.EClo (v_, s))), s))

    let rec ctxSub = function
      | [], s -> []
      | d_ :: g_, s -> I.decSub (d_, s) :: ctxSub (g_, I.dot1 s)

    let rec appendCtx = function
      | gb1_, t_, [] -> gb1_
      | (g1_, b1_), t_, d_ :: g2_ ->
          appendCtx ((I.Decl (g1_, d_), I.Decl (b1_, t_)), t_, g2_)

    let rec createCtx = function
      | (g_, b_), [], s -> ((g_, b_), s, function af_ -> af_)
      | (g_, b_), n :: ll, s -> (
          let (F.LabelDec (l, g1_, g2_)) = F.labelLookup n in
          let t = someEVars (g_, g1_, I.id) in
          let g2'_ = ctxSub (g2_, t) in
          let g'_, b'_ = appendCtx ((g_, b_), S.Parameter (Some n), g2'_) in
          let s' = I.comp (s, I.Shift (List.length g2'_)) in
          let gb''_, s'', af'' = createCtx ((g'_, b'_), ll, s') in
          ( gb''_,
            s'',
            function af_ -> A.Block ((g_, t, List.length g1_, g2'_), af'' af_)
          ))

    let rec createEVars = function
      | g_, I.Null -> I.Shift (I.ctxLength g_)
      | g_, I.Decl (g0_, I.Dec (_, v_)) ->
          let s = createEVars (g_, g0_) in
          I.Dot (I.Exp (I.newEVar (g_, I.EClo (v_, s))), s)

    let rec checkCtx = function
      | g_, [], (v2_, s) -> false
      | g_, (I.Dec (_, v1_) as d_) :: g2_, (v2_, s) ->
          Cs_manager.trail (function () ->
              Unify.unifiable (g_, (v1_, I.id), (v2_, s)))
          || checkCtx (I.Decl (g_, d_), g2_, (v2_, I.comp (s, I.shift)))

    let rec checkLabels ((g'_, b'_), (v_, s), ll, l) =
      begin if l < 0 then None
      else
        let (F.LabelDec (name, g1_, g2_)) = F.labelLookup l in
        let s = someEVars (g'_, g1_, I.id) in
        let g2'_ = ctxSub (g2_, s) in
        let t = someEVars (g'_, g1_, I.id) in
        let g2'_ = ctxSub (g2_, t) in
        begin if
          (not (List.exists (function l' -> l = l') ll))
          && checkCtx (g'_, g2'_, (v_, s))
        then Some l
        else checkLabels ((g'_, b'_), (v_, s), ll, l - 1)
        end
      end

    let rec appendRL = function
      | [], ds_ -> ds_
      | (Lemma (n, f_) as l_) :: ds1_, ds2_ ->
          let ds'_ = appendRL (ds1_, ds2_) in
          begin if
            List.exists
              (function
                | Lemma (n', f'_) ->
                    n = n' && F.convFor ((f_, I.id), (f'_, I.id)))
              ds'_
          then ds'_
          else l_ :: ds'_
          end

    let rec recursion
        ((nih, gall_, fex_, oex_), (ncurrent, (g0_, b0_), ll, ocurrent_, h_, f_))
        =
      let (g'_, b'_), s', af = createCtx ((g0_, b0_), ll, I.id) in
      let t' = createEVars (g'_, gall_) in
      let af_ = af (A.Head (g'_, (fex_, t'), I.ctxLength gall_)) in
      let oex'_ = S.orderSub (oex_, t') in
      let ocurrent'_ = S.orderSub (ocurrent_, s') in
      let rec sc ds_ =
        let fnew_ = A.abstractApproxFor af_ in
        begin if
          List.exists
            (function
              | nhist, fhist_ ->
                  nih = nhist && F.convFor ((fnew_, I.id), (fhist_, I.id)))
            h_
        then ds_
        else Lemma (nih, fnew_) :: ds_
        end
      in
      let rec ac ((g'_, b'_), vs_, ds_) =
        begin match checkLabels ((g'_, b'_), vs_, ll, F.labelSize () - 1) with
        | None -> ds_
        | Some l' ->
            let ds'_ =
              recursion
                ( (nih, gall_, fex_, oex_),
                  (ncurrent, (g0_, b0_), l' :: ll, ocurrent_, h_, f_) )
            in
            appendRL (ds'_, ds_)
        end
      in
      begin if ncurrent < nih then
        ordle ((g'_, b'_), oex'_, ocurrent'_, sc, ac, [])
      else ordlt ((g'_, b'_), oex'_, ocurrent'_, sc, ac, [])
      end

    and set_parameter
        (((g1_, b1_) as gb_), (I.EVar (r, _, v_, _) as x_), k, sc, ac, ds_) =
      let rec set_parameter' = function
        | (I.Null, I.Null), _, ds_ -> ds_
        | (I.Decl (g_, d_), I.Decl (b_, S.Parameter _)), k, ds_ ->
            let (I.Dec (_, v'_) as d'_) = I.decSub (d_, I.Shift k) in
            let ds'_ =
              Cs_manager.trail (function () ->
                  begin if
                    Unify.unifiable (g1_, (v_, I.id), (v'_, I.id))
                    && Unify.unifiable
                         (g1_, (x_, I.id), (I.Root (I.BVar k, I.Nil), I.id))
                  then sc ds_
                  else ds_
                  end)
            in
            set_parameter' ((g_, b_), k + 1, ds'_)
        | (I.Decl (g_, d_), I.Decl (b_, _)), k, ds_ ->
            set_parameter' ((g_, b_), k + 1, ds_)
      in
      set_parameter' (gb_, 1, ds_)

    and ltinit (gb_, k, (us_, vs_), usVs'_, sc, ac, ds_) =
      ltinitW (gb_, k, Whnf.whnfEta (us_, vs_), usVs'_, sc, ac, ds_)

    and ltinitW = function
      | gb_, k, (us_, ((I.Root _, _) as vs_)), usVs'_, sc, ac, ds_ ->
          lt (gb_, k, (us_, vs_), usVs'_, sc, ac, ds_)
      | ( (g_, b_),
          k,
          ((I.Lam (d1_, u_), s1), (I.Pi (d2_, v_), s2)),
          ((u'_, s1'), (v'_, s2')),
          sc,
          ac,
          ds_ ) ->
          ltinit
            ( (I.Decl (g_, I.decSub (d1_, s1)), I.Decl (b_, S.Parameter None)),
              k + 1,
              ((u_, I.dot1 s1), (v_, I.dot1 s2)),
              ((u'_, I.comp (s1', I.shift)), (v'_, I.comp (s2', I.shift))),
              sc,
              ac,
              ds_ )

    and lt (gb_, k, (us_, vs_), (us'_, vs'_), sc, ac, ds_) =
      ltW (gb_, k, (us_, vs_), Whnf.whnfEta (us'_, vs'_), sc, ac, ds_)

    and ltW = function
      | gb_, k, (us_, vs_), ((I.Root (I.Const c, s'_), s'), vs'_), sc, ac, ds_
        ->
          ltSpine
            (gb_, k, (us_, vs_), ((s'_, s'), (I.constType c, I.id)), sc, ac, ds_)
      | ( ((g_, b_) as gb_),
          k,
          (us_, vs_),
          ((I.Root (I.BVar n, s'_), s'), vs'_),
          sc,
          ac,
          ds_ ) -> begin
          match I.ctxLookup (b_, n) with
          | S.Parameter _ ->
              let (I.Dec (_, v'_)) = I.ctxDec (g_, n) in
              ltSpine (gb_, k, (us_, vs_), ((s'_, s'), (v'_, I.id)), sc, ac, ds_)
          | S.Lemma _ -> ds_
        end
      | gb_, _, _, ((I.EVar _, _), _), _, _, ds_ -> ds_
      | ( ((g_, b_) as gb_),
          k,
          ((u_, s1), (v_, s2)),
          ( (I.Lam ((I.Dec (_, v1'_) as d_), u'_), s1'),
            (I.Pi ((I.Dec (_, v2'_), _), v'_), s2') ),
          sc,
          ac,
          ds_ ) ->
          let ds'_ = ds_ in
          begin if Subordinate.equiv (I.targetFam v_, I.targetFam v1'_) then
            let x_ = I.newEVar (g_, I.EClo (v1'_, s1')) in
            let sc' = function
              | ds''_ -> set_parameter (gb_, x_, k, sc, ac, ds''_)
            in
            lt
              ( gb_,
                k,
                ((u_, s1), (v_, s2)),
                ((u'_, I.Dot (I.Exp x_, s1')), (v'_, I.Dot (I.Exp x_, s2'))),
                sc',
                ac,
                ds'_ )
          else begin
            if Subordinate.below (I.targetFam v1'_, I.targetFam v_) then
              let x_ = I.newEVar (g_, I.EClo (v1'_, s1')) in
              lt
                ( gb_,
                  k,
                  ((u_, s1), (v_, s2)),
                  ((u'_, I.Dot (I.Exp x_, s1')), (v'_, I.Dot (I.Exp x_, s2'))),
                  sc,
                  ac,
                  ds'_ )
            else ds'_
          end
          end

    and ltSpine (gb_, k, (us_, vs_), (ss'_, vs'_), sc, ac, ds_) =
      ltSpineW (gb_, k, (us_, vs_), (ss'_, Whnf.whnf vs'_), sc, ac, ds_)

    and ltSpineW = function
      | gb_, k, (us_, vs_), ((I.Nil, _), _), _, _, ds_ -> ds_
      | gb_, k, (us_, vs_), ((I.SClo (s_, s'), s''), vs'_), sc, ac, ds_ ->
          ltSpineW
            (gb_, k, (us_, vs_), ((s_, I.comp (s', s'')), vs'_), sc, ac, ds_)
      | ( gb_,
          k,
          (us_, vs_),
          ((I.App (u'_, s'_), s1'), (I.Pi ((I.Dec (_, v1'_), _), v2'_), s2')),
          sc,
          ac,
          ds_ ) ->
          let ds'_ =
            le (gb_, k, (us_, vs_), ((u'_, s1'), (v1'_, s2')), sc, ac, ds_)
          in
          ltSpine
            ( gb_,
              k,
              (us_, vs_),
              ((s'_, s1'), (v2'_, I.Dot (I.Exp (I.EClo (u'_, s1')), s2'))),
              sc,
              ac,
              ds'_ )

    and eq ((g_, b_), (us_, vs_), (us'_, vs'_), sc, ac, ds_) =
      Cs_manager.trail (function () ->
          begin if
            Unify.unifiable (g_, vs_, vs'_) && Unify.unifiable (g_, us_, us'_)
          then sc ds_
          else ds_
          end)

    and le (gb_, k, (us_, vs_), (us'_, vs'_), sc, ac, ds_) =
      let ds'_ = eq (gb_, (us_, vs_), (us'_, vs'_), sc, ac, ds_) in
      leW (gb_, k, (us_, vs_), Whnf.whnfEta (us'_, vs'_), sc, ac, ds'_)

    and leW = function
      | ( ((g_, b_) as gb_),
          k,
          ((u_, s1), (v_, s2)),
          ( (I.Lam ((I.Dec (_, v1'_) as d_), u'_), s1'),
            (I.Pi ((I.Dec (_, v2'_), _), v'_), s2') ),
          sc,
          ac,
          ds_ ) ->
          let ds'_ = ac (gb_, (v1'_, s1'), ds_) in
          begin if Subordinate.equiv (I.targetFam v_, I.targetFam v1'_) then
            let x_ = I.newEVar (g_, I.EClo (v1'_, s1')) in
            let sc' = function
              | ds''_ -> set_parameter (gb_, x_, k, sc, ac, ds''_)
            in
            le
              ( gb_,
                k,
                ((u_, s1), (v_, s2)),
                ((u'_, I.Dot (I.Exp x_, s1')), (v'_, I.Dot (I.Exp x_, s2'))),
                sc',
                ac,
                ds'_ )
          else begin
            if Subordinate.below (I.targetFam v1'_, I.targetFam v_) then
              let x_ = I.newEVar (g_, I.EClo (v1'_, s1')) in
              let sc' = sc in
              let ds''_ =
                le
                  ( gb_,
                    k,
                    ((u_, s1), (v_, s2)),
                    ((u'_, I.Dot (I.Exp x_, s1')), (v'_, I.Dot (I.Exp x_, s2'))),
                    sc',
                    ac,
                    ds'_ )
              in
              ds''_
            else ds'_
          end
          end
      | gb_, k, (us_, vs_), (us'_, vs'_), sc, ac, ds_ ->
          lt (gb_, k, (us_, vs_), (us'_, vs'_), sc, ac, ds_)

    and ordlt = function
      | gb_, S.Arg (usVs_a, usVs_b), S.Arg (usVs'_a, usVs'_b), sc, ac, ds_ ->
          ltinit (gb_, 0, (usVs_a, usVs_b), (usVs'_a, usVs'_b), sc, ac, ds_)
      | gb_, S.Lex l_, S.Lex l'_, sc, ac, ds_ ->
          ordltLex (gb_, l_, l'_, sc, ac, ds_)
      | gb_, S.Simul l_, S.Simul l'_, sc, ac, ds_ ->
          ordltSimul (gb_, l_, l'_, sc, ac, ds_)

    and ordltLex = function
      | gb_, [], [], sc, ac, ds_ -> ds_
      | gb_, o_ :: l_, o'_ :: l'_, sc, ac, ds_ ->
          let ds'_ =
            Cs_manager.trail (function () -> ordlt (gb_, o_, o'_, sc, ac, ds_))
          in
          ordeq
            ( gb_,
              o_,
              o'_,
              (fun ds''_ -> ordltLex (gb_, l_, l'_, sc, ac, ds''_)),
              ac,
              ds'_ )

    and ordltSimul = function
      | gb_, [], [], sc, ac, ds_ -> ds_
      | gb_, o_ :: l_, o'_ :: l'_, sc, ac, ds_ ->
          let ds''_ =
            Cs_manager.trail (function () ->
                ordlt
                  ( gb_,
                    o_,
                    o'_,
                    (fun ds'_ -> ordleSimul (gb_, l_, l'_, sc, ac, ds'_)),
                    ac,
                    ds_ ))
          in
          ordeq
            ( gb_,
              o_,
              o'_,
              (fun ds'_ -> ordltSimul (gb_, l_, l'_, sc, ac, ds'_)),
              ac,
              ds''_ )

    and ordleSimul = function
      | gb_, [], [], sc, ac, ds_ -> sc ds_
      | gb_, o_ :: l_, o'_ :: l'_, sc, ac, ds_ ->
          ordle
            ( gb_,
              o_,
              o'_,
              (fun ds'_ -> ordleSimul (gb_, l_, l'_, sc, ac, ds'_)),
              ac,
              ds_ )

    and ordeq = function
      | (g_, b_), S.Arg (us_, vs_), S.Arg (us'_, vs'_), sc, ac, ds_ -> begin
          if Unify.unifiable (g_, vs_, vs'_) && Unify.unifiable (g_, us_, us'_)
          then sc ds_
          else ds_
        end
      | gb_, S.Lex l_, S.Lex l'_, sc, ac, ds_ ->
          ordeqs (gb_, l_, l'_, sc, ac, ds_)
      | gb_, S.Simul l_, S.Simul l'_, sc, ac, ds_ ->
          ordeqs (gb_, l_, l'_, sc, ac, ds_)

    and ordeqs = function
      | gb_, [], [], sc, ac, ds_ -> sc ds_
      | gb_, o_ :: l_, o'_ :: l'_, sc, ac, ds_ ->
          ordeq
            ( gb_,
              o_,
              o'_,
              (fun ds'_ -> ordeqs (gb_, l_, l'_, sc, ac, ds'_)),
              ac,
              ds_ )

    and ordle (gb_, o_, o'_, sc, ac, ds_) =
      let ds'_ =
        Cs_manager.trail (function () -> ordeq (gb_, o_, o'_, sc, ac, ds_))
      in
      ordlt (gb_, o_, o'_, sc, ac, ds'_)

    let rec skolem = function
      | (du, de), gb_, w, F.True, sc -> (gb_, w)
      | (du, de), gb_, w, F.All (F.Prim d_, f_), sc ->
          skolem
            ( (du + 1, de),
              gb_,
              w,
              f_,
              function
              | s, de' ->
                  let s', v'_, f'_ = sc (s, de') in
                  ( I.dot1 s',
                    (fun v_ ->
                      v'_
                        (Abstract.piDepend
                           ( (Whnf.normalizeDec (d_, s'), I.Meta),
                             Whnf.normalize (v_, I.id) ))),
                    fun f_ -> f'_ (F.All (F.Prim (I.decSub (d_, s')), f_)) ) )
      | (du, de), (g_, b_), w, F.Ex (I.Dec (name, v_), f_), sc ->
          let s', v'_, f'_ = sc (w, de) in
          let v1_ = I.EClo (v_, s') in
          let v2_ = Whnf.normalize (v'_ v1_, I.id) in
          let f1_ = F.Ex (I.Dec (name, v1_), F.True) in
          let f2_ = f'_ f1_ in
          let _ =
            begin if !Global.doubleCheck then FunTypeCheck.isFor (g_, f2_)
            else ()
            end
          in
          let d2_ = I.Dec (None, v2_) in
          let t2_ =
            begin match f2_ with
            | F.All _ -> S.Lemma S.Rl
            | _ -> S.Lemma (S.Splits !MTPGlobal.maxSplit)
            end
          in
          skolem
            ( (du, de + 1),
              (I.Decl (g_, d2_), I.Decl (b_, t2_)),
              I.comp (w, I.shift),
              f_,
              function
              | s, de' ->
                  let s', v'_, f'_ = sc (s, de') in
                  ( I.Dot
                      (I.Exp (I.Root (I.BVar (du + (de' - de)), spine du)), s'),
                    v'_,
                    f'_ ) )

    let rec updateState = function
      | s_, ([], s) -> s_
      | ( (S.State (n, (g_, b_), (ih_, oh_), d, o_, h_, f_) as s_),
          (Lemma (n', frl'_) :: l_, s) ) ->
          let (g''_, b''_), s' =
            skolem
              ( (0, 0),
                (g_, b_),
                I.id,
                F.forSub (frl'_, s),
                function s', _ -> (s', (fun v'_ -> v'_), fun f'_ -> f'_) )
          in
          let s'' = I.comp (s, s') in
          updateState
            ( S.State
                ( n,
                  (g''_, b''_),
                  (ih_, oh_),
                  d,
                  S.orderSub (o_, s'),
                  (n', F.forSub (frl'_, s''))
                  :: map (function n', f'_ -> (n', F.forSub (f'_, s'))) h_,
                  F.forSub (f_, s') ),
              (l_, s'') )

    let rec selectFormula = function
      | n, (g0_, F.All (F.Prim (I.Dec (_, v_) as d_), f_), S.All (_, o_)), s_ ->
          selectFormula (n, (I.Decl (g0_, d_), f_, o_), s_)
      | n, (g0_, F.And (f1_, f2_), S.And (o1_, o2_)), s_ ->
          let n', s'_ = selectFormula (n, (g0_, f1_, o1_), s_) in
          selectFormula (n, (g0_, f2_, o2_), s'_)
      | ( nih,
          (gall_, fex_, oex_),
          (S.State (ncurrent, (g0_, b0_), (_, _), _, ocurrent_, h_, f_) as s_) )
        ->
          let ds_ =
            recursion
              ( (nih, gall_, fex_, oex_),
                (ncurrent, (g0_, b0_), [], ocurrent_, h_, f_) )
          in
          (nih + 1, updateState (s_, (ds_, I.id)))

    let rec expand (S.State (n, (g_, b_), (ih_, oh_), d, o_, h_, f_) as s_) =
      let _ =
        begin if !Global.doubleCheck then FunTypeCheck.isState (Obj.magic s_)
        else ()
        end
      in
      let _, s'_ = selectFormula (1, (I.Null, ih_, oh_), s_) in
      s'_

    let rec apply s_ =
      begin
        begin if !Global.doubleCheck then FunTypeCheck.isState (Obj.magic s_)
        else ()
        end;
        s_
      end

    let rec menu _ =
      "Recursion (calculates ALL new assumptions & residual lemmas)"

    let rec handleExceptions f p_ =
      try f p_ with Order.Error s -> raise (Error s)
  end

  (* Newly created *)
  (* Residual Lemma *)
  (*  spine n = S'

        Invariant:
        S' = n;..;1;Nil
     *)
  (* someEVars (G, G1, s) = s'

       Invariant:
       If  |- G ctx
       and  G |- s : G
       then G |- s' : G, G1
    *)
  (* ctxSub (G, s) = G'

       Invariant:
       If   G2 |- s : G1
       and  G1 |- G ctx
       then G2 |- G' = G[s] ctx

       NOTE, should go into a different module. Code duplication!
    *)
  (* appendCtx ((G1, B1), T, G2) = (G', B')

       Invariant:
       If   |- G1 ctx
       and  G1 |- B1 tags
       and  T tag
       and  G1 |- G2 ctx
       then |- G' = G1, G2 ctx
       and  G' |- B' tags
    *)
  (* createCtx ((G, B), ll, s) = ((G', B'), s', af')

     Invariant:
     If   |- G ctx
     and  G |- B tags
     and  . |- label list
     and  |- G1 ctx
     and  G |- s : G1

     then |- G' : ctx
     and  G' |- B' tags
     and  G' = G, G''
     and  G' |- s' : G1
     and  af : forall . |- AF aux formulas. Ex . |- AF' = {{G''}} AF  auxFor
     *)
  (* G |- s' : G1 *)
  (* G |- G2' ctx *)
  (* . |- G' = G, G2' ctx *)
  (* G' |- s'' : G0 *)
  (* createEVars' (G, G0) = s'

       Invariant :
       If   |- G ctx
       and  |- G0 ctx
       then G |- s' : G0
       and  s' = X1 .. Xn where n = |G0|
    *)
  (* checkCtx (G, G2, (V, s)) = B'

       Invariant:
       If   |- G = G0, G1 ctx
       and  G |- G2 ctx
       and  G |- s : G0
       and  G0 |- V : L
       then B' holds iff
            G1 = V1 .. Vn and G, G1, V1 .. Vi-1 |- Vi unifies with V [s o ^i] : L
    *)
  (* checkLabels ((G', B'), V, ll, l) = lopt'

       Invariant:
       If   |- G' ctx
       and  G' |- B' ctx
       and  G' |- s : G0
       and  G0 |- V : type
       and  . |- ll label list
       and  . |- l label number
       then lopt' = NONE if no context block is applicable
       or   lopt' = SOME l' if context block l' is applicable

       NOTE: For this implementation we only pick the first applicable contextblock.
       It is not yet clear what should happen if there are inductive calls where more
       then one contextblocks are introduced --cs
    *)
  (* as nil *)
  (* G' |- t : G1 *)
  (* G |- G2' ctx *)
  (*      | checkLabels _ = NONE   more than one context block is introduced  *)
  (* appendRL (Ds1, Ds2) = Ds'

       Invariant:
       Ds1, Ds2 are a list of residual lemmas
       Ds' = Ds1 @ Ds2, where all duplicates are removed
    *)
  (* recursion ((nih, Gall, Fex, Oex), (ncurrent, (G0, B0), ll, Ocurrent, H, F)) = Ds

       Invariant:

       If

       nih  is the id or the induction hypothesis
       |- Gall ctx
       Gall |- Fex : for        (Fex doesn't contain any universal quantifiers)
       Gall |- Oex : order

       and
       ncurrent is the id of the current proof goal
       |- G0 ctx
       G0 |- B0 tags
       . |- ll label list
       G0 |- Ocurrent order
       G0 |- H history
       G0 |- F formula

       then
       G0 |- Ds decs
    *)
  (* G' |- s' : G0 *)
  (* G' |- t' : Gall *)
  (* set_parameter (GB, X, k, sc, ac, S) = S'

       Invariant:
       appends a list of recursion operators to S after
       instantiating X with all possible local parameters (between 1 and k)
    *)
  (* set_parameter' ((G, B), k, Ds) = Ds'

           Invariant:
           If    G1, D < G
        *)
  (* ltinit (GB, k, ((U1, s1), (V2, s2)), ((U3, s3), (V4, s4)), sc, ac, Ds) = Ds'

       Invariant:
       If   G = G0, Gp    (G0, global context, Gp, parameter context)
       and  |Gp| = k
       and  G |- s1 : G1   G1 |- U1 : V1
       and  G |- s2 : G2   G2 |- V2 : L
                G |- s3 : G1   G1 |- U3 : V3
       and  G |- s4 : G2   G2 |- V4 : L
       and  G |- V1[s1] == V2 [s2]
       and  G |- V3[s3] == V4 [s5]
       and  Ds is a set of all all possible states
       and  sc is success continuation
       then Ds' is an extension of Ds, containing all
            recursion operators
    *)
  (* = I.decSub (D2, s2) *)
  (* lt (GB, k, ((U, s1), (V, s2)), (U', s'), sc, ac, Ds) = Ds'

       Invariant:
       If   G = G0, Gp    (G0, global context, Gp, parameter context)
       and  |Gp| = k
       and  G |- s1 : G1   G1 |- U1 : V1   (U1 [s1] in  whnf)
       and  G |- s2 : G2   G2 |- V2 : L    (V2 [s2] in  whnf)
            G |- s3 : G1   G1 |- U3 : V3
       and  G |- s4 : G2   G2 |- V4 : L
       and  k is the length of the local context
       and  G |- V1[s1] == V2 [s2]
       and  G |- V3[s3] == V4 [s5]
       and  Ds is a set of already calculuate possible states
       and  sc is success continuation
           then Ds' is an extension of Ds, containing all
                recursion operators
    *)
  (* Vs is Root!!! *)
  (* (Us',Vs') may not be eta-expanded!!! *)
  (*          if n <= k then   n must be a local variable  *)
  (* k might not be needed any more: Check --cs *)
  (*            else Ds *)
  (* ctxBlock (GB, I.EClo (V1', s1'), k, sc, ac, Ds) *)
  (* == I.targetFam V2' *)
  (* enforce that X gets only bound to parameters *)
  (* = I.newEVar (I.EClo (V2', s2')) *)
  (* = I.newEVar (I.EClo (V2', s2')) *)
  (* eq (GB, ((U, s1), (V, s2)), (U', s'), sc, ac, Ds) = Ds'

       Invariant:
       If   G |- s1 : G1   G1 |- U1 : V1   (U1 [s1] in  whnf)
       and  G |- s2 : G2   G2 |- V2 : L    (V2 [s2] in  whnf)
            G |- s3 : G1   G1 |- U3 : V3
       and  G |- s4 : G2   G2 |- V4 : L
       and  G |- V1[s1] == V2 [s2]
       and  G |- V3[s3] == V4 [s5]
       and  Ds is a set of already calculuated possible states
       and  sc is success continuation
       then Ds' is an extension of Ds, containing all
            recursion operators resulting from U[s1] = U'[s']
    *)
  (* le (G, k, ((U, s1), (V, s2)), (U', s'), sc, ac, Ds) = Ds'

       Invariant:
       If   G = G0, Gp    (G0, global context, Gp, parameter context)
       and  |Gp| = k
       and  G |- s1 : G1   G1 |- U1 : V1   (U1 [s1] in  whnf)
       and  G |- s2 : G2   G2 |- V2 : L    (V2 [s2] in  whnf)
                G |- s3 : G1   G1 |- U3 : V3
       and  G |- s4 : G2   G2 |- V4 : L
       and  k is the length of the local context
       and  G |- V1[s1] == V2 [s2]
       and  G |- V3[s3] == V4 [s5]
       and  Ds is a set of already calculuated possible states
       and  sc is success continuation
       then Ds' is an extension of Ds, containing all
            recursion operators resulting from U[s1] <= U'[s']
    *)
  (* == I.targetFam V2' *)
  (* = I.newEVar (I.EClo (V2', s2')) *)
  (* enforces that X can only bound to parameter *)
  (* = I.newEVar (I.EClo (V2', s2')) *)
  (*              val sc'' = fn Ds'' => set_parameter (GB, X, k, sc, ac, Ds'')    BUG -cs 
                val Ds''' =  le (GB, k, ((U, s1), (V, s2)),
                                 ((U', I.Dot (I.Exp (X), s1')),
                                  (V', I.Dot (I.Exp (X), s2'))), sc'', ac, Ds'') *)
  (* ordlt (GB, O1, O2, sc, ac, Ds) = Ds'

       Invariant:
       If   G |- O1 augmented subterms
       and  G |- O2 augmented subterms
       and  Ds is a set of already calculuated possible states
       and  sc is success continuation
       then Ds' is an extension of Ds, containing all
            recursion operators of all instantiations of EVars s.t. O1 is
            lexicographically smaller than O2
    *)
  (* ordltLex (GB, L1, L2, sc, ac, Ds) = Ds'

       Invariant:
       If   G |- L1 list of augmented subterms
       and  G |- L2 list of augmented subterms
       and  Ds is a set of already calculuated possible states
       and  sc is success continuation
       then Ds' is an extension of Ds, containing all
            recursion operators of all instantiations of EVars s.t. L1 is
            lexicographically less then L2
    *)
  (* ordltSimul (GB, L1, L2, sc, ac, Ds) = Ds'

       Invariant:
       If   G |- L1 list of augmented subterms
       and  G |- L2 list of augmented subterms
       and  Ds is a set of already calculuated possible states
       and  sc is success continuation
       then Ds' is an extension of Ds, containing all
            recursion operators of all instantiations of EVars s.t. L1 is
            simultaneously smaller than L2
    *)
  (* ordleSimul (GB, L1, L2, sc, ac, Ds) = Ds'

       Invariant:
       If   G |- L1 list of augmented subterms
       and  G |- L2 list of augmented subterms
       and  Ds is a set of already calculuated possible states
       and  sc is success continuation
       then Ds' is an extension of Ds, containing all
            recursion operators of all instantiations of EVars s.t. L1 is
            simultaneously smaller than or equal to L2
    *)
  (* ordeq (GB, O1, O2, sc, ac, Ds) = Ds'

       Invariant:
       If   G |- O1 augmented subterms
       and  G |- O2 augmented subterms
       and  Ds is a set of already calculuated possible states
       and  sc is success continuation
       then Ds' is an extension of Ds, containing all
            recursion operators of all instantiations of EVars s.t. O1 is
            convertible to O2
    *)
  (* ordlteqs (GB, L1, L2, sc, ac, Ds) = Ds'

       Invariant:
       If   G |- L1 list of augmented subterms
       and  G |- L2 list of augmented subterms
       and  Ds is a set of already calculuated possible states
       and  sc is success continuation
       then Ds' is an extension of Ds, containing all
            recursion operators of all instantiations of EVars s.t. L1 is
            convertible to L2
    *)
  (* ordeq (GB, O1, O2, sc, ac, Ds) = Ds'

       Invariant:
       If   G |- O1 augmented subterms
       and  G |- O2 augmented subterms
       and  Ds is a set of already calculuated possible states
       and  sc is success continuation
       then Ds' is an extension of Ds, containing all
            recursion operators of all instantiations of EVars s.t. O1 is
            convertible to O2 or smaller than O2
    *)
  (* skolem (n, (du, de), GB, w, F, sc) = (GB', s')

       Invariant:
       If   GB, Ds |- w : GB
       and  GB, G |- F formula
       and  du = #universal quantifiers in F
       and  de = #existential quantifiers in F
       and  sc is a continuation which
            for all GB, Ds |- s' : GB
            returns s''  of type  GB, Ds, G'[...] |- w'' : GB, G
            and     V''  mapping (GB, Ds, G'[...] |- V  type)  to (GB, Ds |- {G'[...]} V type)
            and     F''  mapping (GB, Ds, G'[...] |- F) to (GB, Ds |- {{G'[...]}} F formula)
       then GB' = GB, Ds'
       and  |Ds'| = de
       and  each declaration in Ds' corresponds to one existential quantifier in F
       and  GB' |- s' : GB
    *)
  (* s'  :  GB, Ds |- s : GB   *)
  (* s'  : GB, Ds, G'[...] |- s' : GB, G *)
  (* V'  : maps (GB, Ds, G'[...] |- V type) to (GB, Ds |- {G'[...]} V type) *)
  (* F'  : maps (GB, Ds, G'[...] |- F for) to (GB, Ds |- {{G'[...]}} F for) *)
  (* _   : GB, Ds, G'[...], D[?] |- _ : GB, G, D *)
  (* _   : maps (GB, Ds, G'[....], D[?] |- V : type) to  (GB, Ds, |- {G[....], D[?]} V : type) *)
  (* _   : maps (GB, Ds, G'[....], D[?] |- F : for) to  (GB, Ds, |- {{G[....], D[?]}} F : for) *)
  (* V   : GB, G |- V type *)
  (* s'  : GB, Ds, G'[...] |- s' : GB, G *)
  (* V'  : maps  (GB, Ds, G'[...] |- V : type)   to   (GB, Ds |- {G'[...]} V : type) *)
  (* F'  : maps  (GB, Ds, G'[...] |- F : for)    to   (GB, Ds |- {{G'[...]}} F : for) *)
  (* V1  : GB, Ds, G'[...] |- V1 = V [s'] : type *)
  (* V2  : GB, Ds |- {G'[...]} V2 : type *)
  (* F1  : GB, Ds, G'[...] |- F1 : for *)
  (* F2  : GB, Ds |- {{G'[...]}} F2 : for *)
  (* D2  : GB, Ds |- D2 : type *)
  (* T2  : GB, Ds |- T2 : tag *)
  (* s   : GB, Ds, D2 |- s : GB *)
  (* s'  : GB, Ds, D2, G'[...] |- s' : GB, G *)
  (* V'  : maps (GB, Ds, D2, G'[...] |- V type) to (GB, Ds, D2 |- {G'[...]} V type) *)
  (* F'  : maps (GB, Ds, D2, G'[...] |- F for) to (GB, Ds, D2 |- {{G'[...]}} F for) *)
  (* _ : GB, Ds, D2, G'[...] |- s'' : GB, G, D *)
  (* updateState (S, (Ds, s))

       Invariant:
       G context
       G' |- S state
       G |- Ds new decs
       G' |- s : G
    *)
  (* selectFormula (n, G, (G0, F, O), S) = S'

       Invariant:
       If   G |- s : G0  and  G0 |- F formula and  G0 |- O order
       and  S is a state
       then S' is the state with
       sc returns with all addition assumptions/residual lemmas for a certain
       branch of the theorem.
    *)
  let expand = handleExceptions expand
  let apply = apply
  let menu = menu
end
(*! sharing FunPrint.FunSyn = FunSyn !*)
(*! structure Cs_manager : CS_MANAGER !*)
(*! sharing Cs_manager.IntSyn = IntSyn !*)
(* local *)
(* functor MTPRecursion *)

(* # 1 "src/meta/mtp_recursion.sml.ml" *)
