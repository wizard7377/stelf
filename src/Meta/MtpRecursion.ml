open! Global.Global_
open! Intsyn.Lambda_
open! Names.Names_
open! Formatter.Formatter_
open! Print.Print_
open! Subordinate
open! Typecheck.Typecheck_
open! Solvers.Solvers_

(* # 1 "src/meta/Recursion.sig.ml" *)
open Funsyn
open Statesyn
open MtpGlobal
open MtpAbstract
open MtpPrint
open Funtypecheck
open Funprint

(* Recursion: Version 1.3 *)
(* Author: Carsten Schuermann *)
include MTPRECURSION
(* signature MTPRECURSION *)

(* # 1 "src/meta/Recursion.fun.ml" *)
open! Basis

(* Meta Recursion Version 1.3 *)
(* Author: Carsten Schuermann *)
(* See [Rohwedder,Pfenning ESOP'96] *)
exception Error of string

let () =
  Printexc.register_printer (function Error msg -> Some msg | _ -> None)

module MTPRecursion (MTPRecursion__0 : sig
  module MTPGlobal : MtpGlobal.MTPGLOBAL
  module Global : GLOBAL

  (*! structure IntSyn : INTSYN !*)
  (*! structure FunSyn : FUNSYN !*)
  (*! sharing FunSyn.IntSyn = IntSyn !*)
  module StateSyn' : STATESYN.STATESYN

  (*! sharing StateSyn'.IntSyn = IntSyn !*)
  (*! sharing StateSyn'.FunSyn = FunSyn !*)
  module Abstract : ABSTRACT

  (*! sharing Abstract.IntSyn = IntSyn !*)
  module MTPAbstract : MTPABSTRACT.MTPABSTRACT

  (*! sharing MTPAbstract.IntSyn = IntSyn !*)
  (*! sharing MTPAbstract.FunSyn = FunSyn !*)
  module FunTypeCheck : FUNTYPECHECK.FUNTYPECHECK

  (*! sharing FunTypeCheck.FunSyn = FunSyn !*)
  module MTPrint : MTPPRINT.MTPRINT
  module Whnf : WHNF

  (*! sharing Whnf.IntSyn = IntSyn !*)
  module Unify : UNIFY

  (*! sharing Unify.IntSyn = IntSyn !*)
  module Conv : CONV

  (*! sharing Conv.IntSyn = IntSyn !*)
  module Names : NAMES

  (*! sharing Names.IntSyn = IntSyn !*)
  module Subordinate : Subordinate_.SUBORDINATE

  (*! sharing Subordinate.IntSyn = IntSyn !*)
  module Print : PRINT

  (*! sharing Print.IntSyn = IntSyn !*)
  module TypeCheck : TYPECHECK

  (*! sharing TypeCheck.IntSyn = IntSyn !*)
  module Formatter : FORMATTER
  module FunPrint : FUNPRINT.FUNPRINT
end) : MTPRECURSION = struct
  open MTPRecursion__0
  module StateSyn = StateSyn'

  exception Error = Error

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
      | I.Decl (g, d) ->
          begin if Abstract.closedDec g (d, I.id) then raise Domain
          else closedCtx g
          end

    let rec spine = function
      | 0 -> I.Nil
      | n -> I.App (I.Root (I.BVar n, I.Nil), spine (n - 1))

    let rec someEVars (g, a, s) = match a with
      | [] -> s
      | I.Dec (_, v) :: l ->
          someEVars (g, l, I.Dot (I.Exp (I.newEVar g (I.EClo (v, s))), s))

    let rec ctxSub (a, s) = match a with
      | [] -> []
      | d :: g -> I.decSub d s :: ctxSub (g, I.dot1 s)

    let rec appendCtx (gb1, t, a) = match gb1, a with
      | gb1, [] -> gb1
      | (g1, b1), d :: g2 ->
          appendCtx ((I.Decl (g1, d), I.Decl (b1, t)), t, g2)

    let rec createCtx (a, b, s) = match a, b with
      | (g, b), [] -> ((g, b), s, function af -> af)
      | (g, b), n :: ll -> (
          let (F.LabelDec (l, g1, g2)) = F.labelLookup n in
          let t = someEVars (g, g1, I.id) in
          let g2' = ctxSub (g2, t) in
          let g', b' = appendCtx ((g, b), S.Parameter (Some n), g2') in
          let s' = I.comp s (I.Shift (List.length g2')) in
          let gb'', s'', af'' = createCtx ((g', b'), ll, s') in
          ( gb'',
            s'',
            function af -> A.Block ((g, t, List.length g1, g2'), af'' af)
          ))

    let rec createEVars (g, a) = match a with
      | I.Null -> I.Shift (I.ctxLength g)
      | I.Decl (g0, I.Dec (_, v)) ->
          let s = createEVars (g, g0) in
          I.Dot (I.Exp (I.newEVar g (I.EClo (v, s))), s)

    let rec checkCtx (g, a, b) = match a, b with
      | [], (v2, s) -> false
      | (I.Dec (_, v1) as d) :: g2, (v2, s) ->
          CsManager.trail (function () ->
              Unify.unifiable g (v1, I.id) (v2, s))
          || checkCtx (I.Decl (g, d), g2, (v2, I.comp s I.shift))

    let rec checkLabels ((g', b'), (v, s), ll, l) =
      begin if l < 0 then None
      else
        let (F.LabelDec (name, g1, g2)) = F.labelLookup l in
        let s = someEVars (g', g1, I.id) in
        let g2' = ctxSub (g2, s) in
        let t = someEVars (g', g1, I.id) in
        let g2' = ctxSub (g2, t) in
        begin if
          (not (List.exists (function l' -> l = l') ll))
          && checkCtx (g', g2', (v, s))
        then Some l
        else checkLabels ((g', b'), (v, s), ll, l - 1)
        end
      end

    let rec appendRL = function
      | [], ds -> ds
      | (Lemma (n, f) as l) :: ds1, ds2 ->
          let ds' = appendRL (ds1, ds2) in
          begin if
            List.exists
              (function
                | Lemma (n', f') ->
                    n = n' && F.convFor f I.id (f', I.id))
              ds'
          then ds'
          else l :: ds'
          end

    let rec recursion
        ((nih, gall, fex, oex), (ncurrent, (g0, b0), ll, ocurrent, h, f)) =
      let (g', b'), s', af = createCtx ((g0, b0), ll, I.id) in
      let t' = createEVars (g', gall) in
      let af_ = af (A.Head (g', (fex, t'), I.ctxLength gall)) in
      let oex' = S.orderSub oex t' in
      let ocurrent' = S.orderSub ocurrent s' in
      let sc ds =
        let fnew = A.abstractApproxFor af_ in
        begin if
          List.exists
            (function
              | nhist, fhist ->
                  nih = nhist && F.convFor fnew I.id (fhist, I.id))
            h
        then ds
        else Lemma (nih, fnew) :: ds
        end
      in
      let ac ((g', b'), vs, ds) =
        begin match checkLabels ((g', b'), vs, ll, F.labelSize () - 1) with
        | None -> ds
        | Some l' ->
            let ds' =
              recursion
                ( (nih, gall, fex, oex),
                  (ncurrent, (g0, b0), l' :: ll, ocurrent, h, f) )
            in
            appendRL (ds', ds)
        end
      in
      begin if ncurrent < nih then
        ordle ((g', b'), oex', ocurrent', sc, ac, [])
      else ordlt ((g', b'), oex', ocurrent', sc, ac, [])
      end

    and set_parameter
        (((g1, b1) as gb), (I.EVar (r, _, v, _) as x), k, sc, ac, ds) =
      let rec set_parameter' (a, k, ds) = match a with
        | (I.Null, I.Null) -> ds
        | (I.Decl (g, d), I.Decl (b, S.Parameter _)) ->
            let (I.Dec (_, v') as d') = I.decSub d (I.Shift k) in
            let ds' =
              CsManager.trail (function () ->
                  begin if
                    Unify.unifiable g1 (v, I.id) (v', I.id)
                    && Unify.unifiable
                         g1 (x, I.id) (I.Root (I.BVar k, I.Nil), I.id)
                  then sc ds
                  else ds
                  end)
            in
            set_parameter' ((g, b), k + 1, ds')
        | (I.Decl (g, d), I.Decl (b, _)) ->
            set_parameter' ((g, b), k + 1, ds)
      in
      set_parameter' (gb, 1, ds)

    and ltinit (gb, k, (us, vs), usVs', sc, ac, ds) =
      ltinitW (gb, k, Whnf.whnfEta us vs, usVs', sc, ac, ds)

    and ltinitW (gb, k, a, usVs', sc, ac, ds) = match gb, a, usVs' with
      | gb, (us, ((I.Root _, _) as vs)), usVs' ->
          lt (gb, k, (us, vs), usVs', sc, ac, ds)
      | (g, b), ((I.Lam (d1, u), s1), (I.Pi (d2, v), s2)), ((u', s1'), (v', s2')) ->
          ltinit
            ( (I.Decl (g, I.decSub d1 s1), I.Decl (b, S.Parameter None)),
              k + 1,
              ((u, I.dot1 s1), (v, I.dot1 s2)),
              ((u', I.comp s1' I.shift), (v', I.comp s2' I.shift)),
              sc,
              ac,
              ds )

    and lt (gb, k, (us, vs), (us', vs'), sc, ac, ds) =
      ltW (gb, k, (us, vs), Whnf.whnfEta us' vs', sc, ac, ds)

    and ltW (a, k, b, d, sc, ac, ds) = match a, b, d with
      | gb, (us, vs), ((I.Root (I.Const c, s'_), s'), vs') ->
          ltSpine
            (gb, k, (us, vs), ((s'_, s'), (I.constType c, I.id)), sc, ac, ds)
      | ((g, b) as gb), (us, vs), ((I.Root (I.BVar n, s'_), s'), vs') ->
          begin match I.ctxLookup b n with
          | S.Parameter _ ->
              let (I.Dec (_, v')) = I.ctxDec g n in
              ltSpine (gb, k, (us, vs), ((s'_, s'), (v', I.id)), sc, ac, ds)
          | S.Lemma _ -> ds
          end
      | gb, _, ((I.EVar _, _), _) -> ds
      | ((g, b) as gb), ((u, s1), (v, s2)), ( (I.Lam ((I.Dec (_, v1') as d), u'), s1'),
            (I.Pi ((I.Dec (_, v2'), _), v'), s2') ) ->
          let ds' = ds in
          begin if Subordinate.equiv (I.targetFam v) (I.targetFam v1') then
            let x = I.newEVar g (I.EClo (v1', s1')) in
            let sc' = function
              | ds'' -> set_parameter (gb, x, k, sc, ac, ds'')
            in
            lt
              ( gb,
                k,
                ((u, s1), (v, s2)),
                ((u', I.Dot (I.Exp x, s1')), (v', I.Dot (I.Exp x, s2'))),
                sc',
                ac,
                ds' )
          else
            begin if Subordinate.below (I.targetFam v1') (I.targetFam v) then
              let x = I.newEVar g (I.EClo (v1', s1')) in
              lt
                ( gb,
                  k,
                  ((u, s1), (v, s2)),
                  ((u', I.Dot (I.Exp x, s1')), (v', I.Dot (I.Exp x, s2'))),
                  sc,
                  ac,
                  ds' )
            else ds'
            end
          end

    and ltSpine (gb, k, (us, vs), (ss', vs'), sc, ac, ds) =
      ltSpineW (gb, k, (us, vs), (ss', Whnf.whnf vs'), sc, ac, ds)

    and ltSpineW (gb, k, a, b, sc, ac, ds) = match a, b with
      | (us, vs), ((I.Nil, _), _) -> ds
      | (us, vs), ((I.SClo (s, s'), s''), vs') ->
          ltSpineW
            (gb, k, (us, vs), ((s, I.comp s' s''), vs'), sc, ac, ds)
      | (us, vs), ((I.App (u', s'), s1'), (I.Pi ((I.Dec (_, v1'), _), v2'), s2')) ->
          let ds' =
            le (gb, k, (us, vs), ((u', s1'), (v1', s2')), sc, ac, ds)
          in
          ltSpine
            ( gb,
              k,
              (us, vs),
              ((s', s1'), (v2', I.Dot (I.Exp (I.EClo (u', s1')), s2'))),
              sc,
              ac,
              ds' )

    and eq ((g, b), (us, vs), (us', vs'), sc, ac, ds) =
      CsManager.trail (function () ->
          begin if
            Unify.unifiable g vs vs' && Unify.unifiable g us us'
          then sc ds
          else ds
          end)

    and le (gb, k, (us, vs), (us', vs'), sc, ac, ds) =
      let ds' = eq (gb, (us, vs), (us', vs'), sc, ac, ds) in
      leW (gb, k, (us, vs), Whnf.whnfEta us' vs', sc, ac, ds')

    and leW (a, k, b, c, sc, ac, ds) = match a, b, c with
      | ((g, b) as gb), ((u, s1), (v, s2)), ( (I.Lam ((I.Dec (_, v1') as d), u'), s1'),
            (I.Pi ((I.Dec (_, v2'), _), v'), s2') ) ->
          let ds' = ac (gb, (v1', s1'), ds) in
          begin if Subordinate.equiv (I.targetFam v) (I.targetFam v1') then
            let x = I.newEVar g (I.EClo (v1', s1')) in
            let sc' = function
              | ds'' -> set_parameter (gb, x, k, sc, ac, ds'')
            in
            le
              ( gb,
                k,
                ((u, s1), (v, s2)),
                ((u', I.Dot (I.Exp x, s1')), (v', I.Dot (I.Exp x, s2'))),
                sc',
                ac,
                ds' )
          else
            begin if Subordinate.below (I.targetFam v1') (I.targetFam v) then
              let x = I.newEVar g (I.EClo (v1', s1')) in
              let sc' = sc in
              let ds'' =
                le
                  ( gb,
                    k,
                    ((u, s1), (v, s2)),
                    ((u', I.Dot (I.Exp x, s1')), (v', I.Dot (I.Exp x, s2'))),
                    sc',
                    ac,
                    ds' )
              in
              ds''
            else ds'
            end
          end
      | gb, (us, vs), (us', vs') ->
          lt (gb, k, (us, vs), (us', vs'), sc, ac, ds)

    and ordlt (gb, a, b, sc, ac, ds) = match a, b with
      | S.Arg (usVs_a, usVs_b), S.Arg (usVs'_a, usVs'_b) ->
          ltinit (gb, 0, (usVs_a, usVs_b), (usVs'_a, usVs'_b), sc, ac, ds)
      | S.Lex l, S.Lex l' ->
          ordltLex (gb, l, l', sc, ac, ds)
      | S.Simul l, S.Simul l' ->
          ordltSimul (gb, l, l', sc, ac, ds)

    and ordltLex (gb, a, b, sc, ac, ds) = match a, b with
      | [], [] -> ds
      | o :: l, o' :: l' ->
          let ds' =
            CsManager.trail (function () -> ordlt (gb, o, o', sc, ac, ds))
          in
          ordeq
            ( gb,
              o,
              o',
              (fun ds'' -> ordltLex (gb, l, l', sc, ac, ds'')),
              ac,
              ds' )

    and ordltSimul (gb, a, b, sc, ac, ds) = match a, b with
      | [], [] -> ds
      | o :: l, o' :: l' ->
          let ds'' =
            CsManager.trail (function () ->
                ordlt
                  ( gb,
                    o,
                    o',
                    (fun ds' -> ordleSimul (gb, l, l', sc, ac, ds')),
                    ac,
                    ds ))
          in
          ordeq
            ( gb,
              o,
              o',
              (fun ds' -> ordltSimul (gb, l, l', sc, ac, ds')),
              ac,
              ds'' )

    and ordleSimul (gb, a, b, sc, ac, ds) = match a, b with
      | [], [] -> sc ds
      | o :: l, o' :: l' ->
          ordle
            ( gb,
              o,
              o',
              (fun ds' -> ordleSimul (gb, l, l', sc, ac, ds')),
              ac,
              ds )

    and ordeq (gb, a, b, sc, ac, ds) = match gb, a, b with
      | (g, b), S.Arg (us, vs), S.Arg (us', vs') ->
          begin if
            Unify.unifiable g vs vs' && Unify.unifiable g us us'
          then sc ds
          else ds
          end
      | gb, S.Lex l, S.Lex l' -> ordeqs (gb, l, l', sc, ac, ds)
      | gb, S.Simul l, S.Simul l' ->
          ordeqs (gb, l, l', sc, ac, ds)

    and ordeqs (gb, a, b, sc, ac, ds) = match a, b with
      | [], [] -> sc ds
      | o :: l, o' :: l' ->
          ordeq
            ( gb,
              o,
              o',
              (fun ds' -> ordeqs (gb, l, l', sc, ac, ds')),
              ac,
              ds )

    and ordle (gb, o, o', sc, ac, ds) =
      let ds' =
        CsManager.trail (function () -> ordeq (gb, o, o', sc, ac, ds))
      in
      ordlt (gb, o, o', sc, ac, ds')

    let rec skolem (a, gb, w, b, sc) = match a, gb, b with
      | (du, de), gb, F.True -> (gb, w)
      | (du, de), gb, F.All (F.Prim d, f) ->
          skolem
            ( (du + 1, de),
              gb,
              w,
              f,
              function
              | s, de' ->
                  let s', v', f' = sc (s, de') in
                  ( I.dot1 s',
                    (fun v ->
                      v'
                        (Abstract.piDepend
                           (Whnf.normalizeDec d s') I.Meta (Whnf.normalize (v, I.id)))),
                    fun f -> f' (F.All (F.Prim (I.decSub d s'), f)) ) )
      | (du, de), (g, b), F.Ex (I.Dec (name, v), f) ->
          let s', v', f' = sc (w, de) in
          let v1 = I.EClo (v, s') in
          let v2 = Whnf.normalize (v' v1, I.id) in
          let f1 = F.Ex (I.Dec (name, v1), F.True) in
          let f2 = f' f1 in
          ignore begin if !Global.doubleCheck then FunTypeCheck.isFor g f2
            else ()
            end;
          let d2 = I.Dec (None, v2) in
          let t2 =
            begin match f2 with
            | F.All _ -> S.Lemma S.Rl
            | _ -> S.Lemma (S.Splits !MTPGlobal.maxSplit)
            end
          in
          skolem
            ( (du, de + 1),
              (I.Decl (g, d2), I.Decl (b, t2)),
              I.comp w I.shift,
              f,
              function
              | s, de' ->
                  let s', v', f' = sc (s, de') in
                  ( I.Dot
                      (I.Exp (I.Root (I.BVar (du + (de' - de)), spine du)), s'),
                    v',
                    f' ) )

    let rec updateState = function
      | s_, ([], s) -> s_
      | ( (S.State (n, (g, b), (ih, oh), d, o, h, f) as s_),
          (Lemma (n', frl') :: l, s) ) ->
          let (g'', b''), s' =
            skolem
              ( (0, 0),
                (g, b),
                I.id,
                F.forSub frl' s,
                function s', _ -> (s', (fun v' -> v'), fun f' -> f') )
          in
          let s'' = I.comp s s' in
          updateState
            ( S.State
                ( n,
                  (g'', b''),
                  (ih, oh),
                  d,
                  S.orderSub o s',
                  (n', F.forSub frl' s'')
                  :: map (function n', f' -> (n', F.forSub f' s')) h,
                  F.forSub f s' ),
              (l, s'') )

    let rec selectFormula = function
      | n, (g0, F.All (F.Prim (I.Dec (_, v) as d), f), S.All (_, o)), s ->
          selectFormula (n, (I.Decl (g0, d), f, o), s)
      | n, (g0, F.And (f1, f2), S.And (o1, o2)), s ->
          let n', s' = selectFormula (n, (g0, f1, o1), s) in
          selectFormula (n, (g0, f2, o2), s')
      | ( nih,
          (gall, fex, oex),
          (S.State (ncurrent, (g0, b0), (_, _), _, ocurrent, h, f) as s) )
        ->
          let ds =
            recursion
              ( (nih, gall, fex, oex),
                (ncurrent, (g0, b0), [], ocurrent, h, f) )
          in
          (nih + 1, updateState (s, (ds, I.id)))

    let expand (S.State (n, (g, b), (ih, oh), d, o, h, f) as s) =
      ignore begin if !Global.doubleCheck then FunTypeCheck.isState (Obj.magic s)
        else ()
        end;
      let _, s' = selectFormula (1, (I.Null, ih, oh), s) in
      s'

    let apply s =
      begin
        begin if !Global.doubleCheck then FunTypeCheck.isState (Obj.magic s)
        else ()
        end;
        s
      end

    let menu _ = "Recursion (calculates ALL new assumptions & residual lemmas)"
    let handleExceptions f p = try f p with Order.Error s -> raise (Error s)
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
(*! structure CsManager : CS_MANAGER !*)
(*! sharing CsManager.IntSyn = IntSyn !*)
(* local *)
(* functor MTPRecursion *)

(* # 1 "src/meta/MtpRecursion.sml.ml" *)
