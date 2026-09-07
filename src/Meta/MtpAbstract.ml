open! Basis
open! Global
open! Global.Global_
open! Trail
open! Trail.Trail_
open! Table
open! Table.Table_
open! Intsyn
open! Intsyn.Lambda_
open! Names
open! Names.Names_
open! Formatter
open! Formatter__Formatter_
open! Print
open! Print.Print_
open! Subordinate
open! Subordinate
open! Modes
open! Modes.Modes_
open! Typecheck
open! Typecheck.Typecheck_
open! Index
open! Index.Index_
open! Opsem
open! Opsem.Opsem_
open! Compile
open! Compile.Compile_
open! Heuristic
open! Heuristic.Heuristic_
open! Timing
open! Timing.Timing_
open! Solvers
open! Solvers.Solvers_
open! M2
open! M2.M2_

(* # 1 "src/meta/Abstract.sig.ml" *)
open! Basis
open Funsyn
open Statesyn
open Funtypecheck

(* Meta Theorem Prover abstraction : Version 1.3 *)
(* Author: Frank Pfenning, Carsten Schuermann *)
include MTPABSTRACT
(* signature MTPABSTRACT *)

(* # 1 "src/meta/Abstract.fun.ml" *)
open! Global
open! Basis

(* Meta Theorem Prover abstraction : Version 1.3 *)
(* Author: Frank Pfenning, Carsten Schuermann *)
exception Error of string

let () =
  Printexc.register_printer (function Error msg -> Some msg | _ -> None)

module MTPAbstract (MTPAbstract__0 : sig
  (*! structure IntSyn' : INTSYN !*)
  (*! structure FunSyn' : FUNSYN !*)
  (*! sharing FunSyn'.IntSyn = IntSyn' !*)
  module StateSyn' : STATESYN.STATESYN

  (*! sharing StateSyn'.FunSyn = FunSyn' !*)
  module Whnf : WHNF

  (*! sharing Whnf.IntSyn = IntSyn' !*)
  module Constraints : CONSTRAINTS

  (*! sharing Constraints.IntSyn = IntSyn' !*)
  module Unify : UNIFY

  (*! sharing Unify.IntSyn = IntSyn' !*)
  module Subordinate : Subordinate_.SUBORDINATE

  (*! sharing Subordinate.IntSyn = IntSyn' !*)
  module TypeCheck : TYPECHECK

  (*! sharing TypeCheck.IntSyn = IntSyn' !*)
  module FunTypeCheck : FUNTYPECHECK.FUNTYPECHECK

  (*! sharing FunTypeCheck.FunSyn = FunSyn' !*)
  module Abstract : ABSTRACT
end) : MTPABSTRACT.MTPABSTRACT = struct
  (*! structure IntSyn = IntSyn' !*)
  (*! structure FunSyn = FunSyn' !*)
  open MTPAbstract__0
  module StateSyn = StateSyn'

  exception Error = Error

  type approxFor =
    | Head of IntSyn.dctx * (FunSyn.for_ * IntSyn.sub) * int
    | Block of (IntSyn.dctx * IntSyn.sub * int * IntSyn.dec list) * approxFor

  (* Approximat formula *)
  (* AF ::= F [s] *)
  (*      | (t, G2), AF *)
  open! struct
    module I = IntSyn
    module F = FunSyn
    module S = StateSyn
    module C = Constraints

    type eBVar =
      | Ev of I.exp option ref * I.exp * S.tag * int
      | Bv of I.dec * S.tag

    let checkEmpty = function
      | [] -> ()
      | cnstrL ->
          begin match C.simplify cnstrL with
          | [] -> ()
          | _ -> raise (Error "Typing ambiguous -- unresolved constraints")
          end

    let eqEVar arg__1 arg__2 =
      begin match (arg__1, arg__2) with
      | I.EVar (r1, _, _, _), Ev (r2, _, _, _) -> r1 == r2
      | _, _ -> false
      end

    let exists p_ k_ =
      let rec exists' = function
        | I.Null -> false
        | I.Decl (k'_, y_) -> p_ y_ || exists' k'_
      in
      exists' k_

    let ( or ) = function
      | I.Maybe, _ -> I.Maybe
      | _, I.Maybe -> I.Maybe
      | I.Meta, _ -> I.Meta
      | _, I.Meta -> I.Meta
      | I.No, I.No -> I.No

    let rec occursInExp (k, a) = match a with
      | I.Uni _ -> I.No
      | I.Pi (dp_, v_) ->
          ( or ) (occursInDecP (k, dp_), occursInExp (k + 1, v_))
      | I.Root (h_, s_) -> occursInHead (k, h_, occursInSpine (k, s_))
      | I.Lam (d_, v_) ->
          ( or ) (occursInDec (k, d_), occursInExp (k + 1, v_))

    and occursInHead (k, a, dp_) = match a, dp_ with
      | I.BVar k', dp_ ->
          begin if k = k' then I.Maybe else dp_
          end
      | I.Const _, dp_ -> dp_
      | I.Def _, dp_ -> dp_
      | I.Skonst _, I.No -> I.No
      | I.Skonst _, I.Meta -> I.Meta
      | I.Skonst _, I.Maybe -> I.Meta

    and occursInSpine (k, a) = match a with
      | I.Nil -> I.No
      | I.App (u_, s_) -> ( or ) (occursInExp (k, u_), occursInSpine (k, s_))

    and occursInDec (k, I.Dec (_, v_)) = occursInExp (k, v_)
    and occursInDecP (k, (d_, _)) = occursInDec (k, d_)

    let piDepend a1 b1 = match a1, b1 with
      | (d_, I.No), v_ -> I.Pi ((d_, I.No), v_)
      | (d_, I.Meta), v_ -> I.Pi ((d_, I.Meta), v_)
      | (d_, I.Maybe), v_ -> I.Pi ((d_, occursInExp (1, v_)), v_)

    let rec weaken a1 b1 = match a1, b1 with
      | I.Null, a -> I.id
      | I.Decl (g'_, (I.Dec (name, v_) as d_)), a ->
          let w' = weaken g'_ a in
          begin if Subordinate.belowEq (I.targetFam v_) a then I.dot1 w'
          else I.comp w' I.shift
          end

    let rec raiseType a1 b1 = match a1, b1 with
      | I.Null, v_ -> v_
      | I.Decl (g_, d_), v_ -> raiseType g_ (I.Pi ((d_, I.Maybe), v_))

    let rec restore = function
      | 0, gp -> (gp, I.Null)
      | n, I.Decl (g_, d_) ->
          let gp', gx' = restore (n - 1, g_) in
          (gp', I.Decl (gx', d_))

    let rec concat (gp, a) = match a with
      | I.Null -> gp
      | I.Decl (g_, d_) -> I.Decl (concat (gp, g_), d_)

    let rec collectExpW (tag_, d, g_, a, k_) = match a with
      | (I.Uni l_, s) -> k_
      | (I.Pi ((d_, _), v_), s) ->
          collectExp
            ( tag_,
              d,
              I.Decl (g_, I.decSub d_ s),
              (v_, I.dot1 s),
              collectDec (tag_, d, g_, (d_, s), k_) )
      | (I.Root (_, s_), s) ->
          collectSpine (S.decrease tag_, d, g_, (s_, s), k_)
      | (I.Lam (d_, u_), s) ->
          collectExp
            ( tag_,
              d,
              I.Decl (g_, I.decSub d_ s),
              (u_, I.dot1 s),
              collectDec (tag_, d, g_, (d_, s), k_) )
      | ((I.EVar (r, gdX, v_, cnstrs) as x_), s) ->
          begin if exists (eqEVar x_) k_ then collectSub (tag_, d, g_, s, k_)
          else
            let gp, gx = restore (I.ctxLength gdX - d, gdX) in
            ignore (checkEmpty !cnstrs);
            let w = weaken gx (I.targetFam v_) in
            let iw = Whnf.invert w in
            let gx' = Whnf.strengthen iw gx in
            let (I.EVar (r', _, _, _) as x'_) =
              I.newEVar (concat (gp, gx')) (I.EClo (v_, iw))
            in
            ignore (Unify.instantiateEVar r (I.EClo (x'_, w)) []);
            let v'_ = raiseType gx' (I.EClo (v_, iw)) in
            collectSub
              ( tag_,
                d,
                g_,
                I.comp w s,
                I.Decl
                  ( collectExp (tag_, d, gp, (v'_, I.id), k_),
                    Ev (r', v'_, tag_, d) ) )
          end
      | (I.FgnExp (csid_, csfe), s) ->
          I.FgnExpStd.fold csid_ csfe
            (function u_, k'_ -> collectExp (tag_, d, g_, (u_, s), k'_))
            k_

    and collectExp (tag_, d, g_, us_, k_) =
      collectExpW (tag_, d, g_, Whnf.whnf us_, k_)

    and collectSpine (tag_, d, g_, a, k_) = match a with
      | (I.Nil, _) -> k_
      | (I.SClo (s_, s'), s) ->
          collectSpine (tag_, d, g_, (s_, I.comp s' s), k_)
      | (I.App (u_, s_), s) ->
          collectSpine
            (tag_, d, g_, (s_, s), collectExp (tag_, d, g_, (u_, s), k_))

    and collectDec (tag_, d, g_, (I.Dec (_, v_), s), k_) =
      collectExp (tag_, d, g_, (v_, s), k_)

    and collectSub (tag_, d, g_, a, k_) = match a with
      | I.Shift _ -> k_
      | I.Dot (I.Idx _, s) -> collectSub (tag_, d, g_, s, k_)
      | I.Dot (I.Exp u_, s) ->
          collectSub (tag_, d, g_, s, collectExp (tag_, d, g_, (u_, I.id), k_))

    let rec abstractEVar (a, depth, b) = match a, b with
      | I.Decl (k'_, Ev (r', _, _, d)), (I.EVar (r, _, _, _) as x_) ->
          begin if r == r' then (I.BVar (depth + 1), d)
          else abstractEVar (k'_, depth + 1, x_)
          end
      | I.Decl (k'_, Bv _), x_ -> abstractEVar (k'_, depth + 1, x_)

    let lookupBV (k_, i) =
      let rec lookupBV' (a, i, k) = match a, i with
        | I.Decl (k_, Ev (r, v_, _, _)), i -> lookupBV' (k_, i, k + 1)
        | I.Decl (k_, Bv _), 1 -> k
        | I.Decl (k_, Bv _), i -> lookupBV' (k_, i - 1, k + 1)
      in
      lookupBV' (k_, i, 1)

    let rec abstractExpW (k_, depth, a) = match a with
      | ((I.Uni l_ as u_), s) -> u_
      | (I.Pi ((d_, p_), v_), s) ->
          piDepend
            (abstractDec (k_, depth, (d_, s)), p_) (abstractExp (k_, depth + 1, (v_, I.dot1 s)))
      | (I.Root ((I.BVar k as h_), s_), s) ->
          begin if k > depth then
            let k' = lookupBV (k_, k - depth) in
            I.Root (I.BVar (k' + depth), abstractSpine (k_, depth, (s_, s)))
          else I.Root (h_, abstractSpine (k_, depth, (s_, s)))
          end
      | (I.Root (h_, s_), s) ->
          I.Root (h_, abstractSpine (k_, depth, (s_, s)))
      | (I.Lam (d_, u_), s) ->
          I.Lam
            ( abstractDec (k_, depth, (d_, s)),
              abstractExp (k_, depth + 1, (u_, I.dot1 s)) )
      | ((I.EVar (_, g_, _, _) as x_), s) ->
          let h_, d = abstractEVar (k_, depth, x_) in
          I.Root (h_, abstractSub (I.ctxLength g_ - d, k_, depth, s, I.Nil))
      | (I.FgnExp (csid_, csfe), s) ->
          I.FgnExpStd.Map.apply csid_ csfe (function u_ ->
              abstractExp (k_, depth, (u_, s)))

    and abstractExp (k_, depth, us_) = abstractExpW (k_, depth, Whnf.whnf us_)

    and abstractSub (n, k_, depth, a, s_) = match a with
      | I.Shift k ->
          begin if n > 0 then
            abstractSub
              (n, k_, depth, I.Dot (I.Idx (k + 1), I.Shift (k + 1)), s_)
          else s_
          end
      | I.Dot (I.Idx k, s) ->
          let h_ =
            begin if k > depth then
              let k' = lookupBV (k_, k - depth) in
              I.BVar (k' + depth)
            else I.BVar k
            end
          in
          abstractSub (n - 1, k_, depth, s, I.App (I.Root (h_, I.Nil), s_))
      | I.Dot (I.Exp u_, s) ->
          abstractSub
            ( n - 1,
              k_,
              depth,
              s,
              I.App (abstractExp (k_, depth, (u_, I.id)), s_) )

    and abstractSpine (k_, depth, a) = match a with
      | (I.Nil, _) -> I.Nil
      | (I.SClo (s_, s'), s) ->
          abstractSpine (k_, depth, (s_, I.comp s' s))
      | (I.App (u_, s_), s) ->
          I.App
            ( abstractExp (k_, depth, (u_, s)),
              abstractSpine (k_, depth, (s_, s)) )

    and abstractDec (k_, depth, (I.Dec (x, v_), s)) =
      I.Dec (x, abstractExp (k_, depth, (v_, s)))

    let rec getLevel = function
      | I.Uni _ -> I.Kind
      | I.Pi (_, u_) -> getLevel u_
      | I.Root _ -> I.Type
      | I.Redex (u_, _) -> getLevel u_
      | I.Lam (_, u_) -> getLevel u_
      | I.EClo (u_, _) -> getLevel u_

    let checkType v_ =
      begin match getLevel v_ with
      | I.Type -> ()
      | _ -> raise (Error "Typing ambiguous -- free type variable")
      end

    let rec abstractCtx = function
      | I.Null -> (I.Null, I.Null)
      | I.Decl (k'_, Ev (_, v'_, (S.Lemma _b as t_), _)) ->
          let v'' = abstractExp (k'_, 0, (v'_, I.id)) in
          ignore (checkType v'');
          let g'_, b'_ = abstractCtx k'_ in
          let d'_ = I.Dec (None, v'') in
          (I.Decl (g'_, d'_), I.Decl (b'_, t_))
      | I.Decl (k'_, Ev (_, v'_, (S.None as t_), _)) ->
          let v'' = abstractExp (k'_, 0, (v'_, I.id)) in
          ignore (checkType v'');
          let g'_, b'_ = abstractCtx k'_ in
          let d'_ = I.Dec (None, v'') in
          (I.Decl (g'_, d'_), I.Decl (b'_, S.None))
      | I.Decl (k'_, Bv (d_, tag_)) ->
          let d'_ = abstractDec (k'_, 0, (d_, I.id)) in
          let g'_, b'_ = abstractCtx k'_ in
          (I.Decl (g'_, d'_), I.Decl (b'_, tag_))

    let rec abstractGlobalSub (k_, a, b) = match a, b with
      | I.Shift _, I.Null -> I.Shift (I.ctxLength k_)
      | I.Shift n, (I.Decl _ as b_) ->
          abstractGlobalSub (k_, I.Dot (I.Idx (n + 1), I.Shift (n + 1)), b_)
      | I.Dot (I.Idx k, s'), I.Decl (b_, (S.Parameter _ as t_)) ->
          I.Dot (I.Idx (lookupBV (k_, k)), abstractGlobalSub (k_, s', b_))
      | I.Dot (I.Exp u_, s'), I.Decl (b_, (S.Lemma _ as t_)) ->
          I.Dot
            ( I.Exp (abstractExp (k_, 0, (u_, I.id))),
              abstractGlobalSub (k_, s', b_) )

    let rec collectGlobalSub (g0_, a, b, collect) = match a, b with
      | I.Shift _, I.Null -> collect
      | s, (I.Decl (_, S.Parameter (Some l)) as b_) ->
          let (F.LabelDec (name, _, g2_)) = F.labelLookup l in
          skip (g0_, List.length g2_, s, b_, collect)
      | I.Dot (I.Exp u_, s), I.Decl (b_, tag_) ->
          collectGlobalSub
            ( g0_,
              s,
              b_,
              function
              | d, k_ -> collect (d, collectExp (tag_, d, g0_, (u_, I.id), k_))
            )

    and skip (a, n, s, b, collect) = match a, n, b with
      | g0_, 0, b_ -> collectGlobalSub (g0_, s, b_, collect)
      | I.Decl (g0_, d_), n, I.Decl (b_, (S.Parameter _ as t_)) ->
          skip
            ( g0_,
              n - 1,
              I.invDot1 s,
              b_,
              function d, k_ -> collect (d + 1, I.Decl (k_, Bv (d_, t_))) )

    let abstractNew ((g0_, b0), s, b_) =
      let cf = collectGlobalSub (g0_, s, b_, function _, k'_ -> k'_) in
      let k_ = cf (0, I.Null) in
      (abstractCtx k_, abstractGlobalSub (k_, s, b_))

    let abstractSubAll (t, b1_, (g0_, b0), s, b_) =
      let rec skip'' (k_, a) = match a with
        | (I.Null, I.Null) -> k_
        | (I.Decl (g0_, d_), I.Decl (b0, tag_)) ->
            I.Decl (skip'' (k_, (g0_, b0)), Bv (d_, tag_))
      in
      let collect2 = collectGlobalSub (g0_, s, b_, function _, k'_ -> k'_) in
      let collect0 =
        collectGlobalSub (I.Null, t, b1_, function _, k'_ -> k'_)
      in
      let k0_ = collect0 (0, I.Null) in
      let k1_ = skip'' (k0_, (g0_, b0)) in
      let d = I.ctxLength g0_ in
      let k_ = collect2 (d, k1_) in
      (abstractCtx k_, abstractGlobalSub (k_, s, b_))

    let rec abstractFor (k_, depth, a) = match a with
      | (F.All (F.Prim d_, f_), s) ->
          F.All
            ( F.Prim (abstractDec (k_, depth, (d_, s))),
              abstractFor (k_, depth + 1, (f_, I.dot1 s)) )
      | (F.Ex (d_, f_), s) ->
          F.Ex
            ( abstractDec (k_, depth, (d_, s)),
              abstractFor (k_, depth + 1, (f_, I.dot1 s)) )
      | (True, s) -> F.True
      | (F.And (f1_, f2_), s) ->
          F.And
            ( abstractFor (k_, depth, (f1_, s)),
              abstractFor (k_, depth, (f2_, s)) )

    let rec allClo (a, f_) = match a with
      | I.Null -> f_
      | I.Decl (gx, d_) -> allClo (gx, F.All (F.Prim d_, f_))

    let rec convert = function
      | I.Null -> I.Null
      | I.Decl (g_, d_) -> I.Decl (convert g_, Bv (d_, S.Parameter None))

    let rec createEmptyB = function
      | 0 -> I.Null
      | n -> I.Decl (createEmptyB (n - 1), S.None)

    let rec lower = function
      | _, 0 -> I.Null
      | I.Decl (g_, d_), n -> I.Decl (lower (g_, n - 1), d_)

    let rec split = function
      | g_, 0 -> (g_, I.Null)
      | I.Decl (g_, d_), n ->
          let g1_, g2_ = split (g_, n - 1) in
          (g1_, I.Decl (g2_, d_))

    let rec shift = function
      | I.Null -> I.shift
      | I.Decl (g_, _) -> I.dot1 (shift g_)

    let rec ctxSub (a, s) = match a with
      | [] -> []
      | d_ :: g_ -> I.decSub d_ s :: ctxSub (g_, I.dot1 s)

    let rec weaken2 (b, a, i) = match b with
      | I.Null -> (I.id, function s_ -> s_)
      | I.Decl (g'_, (I.Dec (name, v_) as d_)) ->
          let w', s'_ = weaken2 (g'_, a, i + 1) in
          begin if Subordinate.belowEq (I.targetFam v_) a then
            (I.dot1 w', function s_ -> I.App (I.Root (I.BVar i, I.Nil), s_))
          else (I.comp w' I.shift, s'_)
          end

    let rec raiseType a1 b1 = match a1, b1 with
      | I.Null, v_ -> v_
      | I.Decl (g_, d_), v_ ->
          raiseType
            g_ (Abstract.piDepend (Whnf.normalizeDec d_ I.id, I.Maybe) v_)

    let rec raiseFor (k, gorig, a, w, sc) = match a with
      | (F.True as f_) -> f_
      | F.Ex (I.Dec (name, v_), f_) ->
          let g_ = F.listToCtx (ctxSub (F.ctxToList gorig, w)) in
          let g = I.ctxLength g_ in
          let s = sc (w, k) in
          let v'_ = I.EClo (v_, s) in
          let nw, s_ = weaken2 (g_, I.targetFam v_, 1) in
          let iw = Whnf.invert nw in
          let gw_ = Whnf.strengthen iw g_ in
          let v'' = Whnf.normalize (v'_, iw) in
          let v''' = Whnf.normalize (raiseType gw_ v'', I.id) in
          let s''' = s_ I.Nil in
          let sc' (w', k') =
                let s' = sc (w', k') in
                I.Dot (I.Exp (I.Root (I.BVar (g + k' - k), s''')), s')
          in
          let f'_ = raiseFor (k + 1, gorig, f_, I.comp w I.shift, sc') in
          F.Ex (I.Dec (name, v'''), f'_)
      | F.All (F.Prim (I.Dec (name, v_)), f_) ->
          let g_ = F.listToCtx (ctxSub (F.ctxToList gorig, w)) in
          let g = I.ctxLength g_ in
          let s = sc (w, k) in
          let v'_ = I.EClo (v_, s) in
          let nw, s_ = weaken2 (g_, I.targetFam v_, 1) in
          let iw = Whnf.invert nw in
          let gw_ = Whnf.strengthen iw g_ in
          let v'' = Whnf.normalize (v'_, iw) in
          let v''' = Whnf.normalize (raiseType gw_ v'', I.id) in
          let s''' = s_ I.Nil in
          let sc' (w', k') =
                let s' = sc (w', k') in
                I.Dot (I.Exp (I.Root (I.BVar (g + k' - k), s''')), s')
          in
          let f'_ = raiseFor (k + 1, gorig, f_, I.comp w I.shift, sc') in
          F.All (F.Prim (I.Dec (name, v''')), f'_)

    let rec extend (k_, a) = match a with
      | [] -> k_
      | d_ :: l_ -> extend (I.Decl (k_, Bv (d_, S.None)), l_)

    let rec makeFor (k_, w, a) = match a with
      | Head (g_, (f_, s), d) ->
          let cf =
            collectGlobalSub (g_, s, createEmptyB d, function _, k'_ -> k'_)
          in
          let k = I.ctxLength k_ in
          let k'_ = cf (I.ctxLength g_, k_) in
          let k' = I.ctxLength k'_ in
          let gk_, bk = abstractCtx k'_ in
          ignore begin if !Global.doubleCheck then TypeCheck.typeCheckCtx gk_ else ()
            end;
          let w' = I.comp w (I.Shift (k' - k)) in
          let fk = abstractFor (k'_, 0, (f_, s)) in
          ignore begin if !Global.doubleCheck then FunTypeCheck.isFor gk_ fk
            else ()
            end;
          let gk1, gk2 = split (gk_, k' - k) in
          (gk1, allClo (gk2, fk))
      | Block ((g_, t, d, g2_), af_) ->
          let k = I.ctxLength k_ in
          let collect =
            collectGlobalSub (g_, t, createEmptyB d, function _, k'_ -> k'_)
          in
          let k'_ = collect (I.ctxLength g_, k_) in
          let k' = I.ctxLength k'_ in
          let k''_ = extend (k'_, g2_) in
          let w' = F.dot1n (F.listToCtx g2_) (I.comp w (I.Shift (k' - k))) in
          let gk_, f'_ = makeFor (k''_, w', af_) in
          ignore begin if !Global.doubleCheck then FunTypeCheck.isFor gk_ f'_
            else ()
            end;
          let gk1, gk2 = split (gk_, List.length g2_) in
          let f''_ =
            raiseFor (0, gk2, f'_, I.id, function w, _ -> F.dot1n gk2 w)
          in
          ignore begin if !Global.doubleCheck then FunTypeCheck.isFor gk1 f''_
            else ()
            end;
          let gk11, gk12 = split (gk1, k' - k) in
          let f'''_ = allClo (gk12, f''_) in
          ignore begin if !Global.doubleCheck then FunTypeCheck.isFor gk11 f'''_
            else ()
            end;
          (gk11, f'''_)

    let abstractApproxFor = function
      | Head (g_, _, _) as af_ ->
          let _, f_ = makeFor (convert g_, I.id, af_) in
          f_
      | Block ((g_, _, _, _), _) as af_ ->
          let _, f_ = makeFor (convert g_, I.id, af_) in
          f_
  end

  (* Intermediate Data Structure *)
  (* y ::= (X , {G2} V)  if {G1, G2 |- X : V
                                          |G1| = d *)
  (*
       We write {{K}} for the context of K, where EVars and BVars have
       been translated to declarations and their occurrences to BVars.
       We write {{U}}_K, {{S}}_K for the corresponding translation of an
       expression or spine.

       Just like contexts G, any K is implicitly assumed to be
       well-formed and in dependency Order.

       We write  K ||- U  if all EVars and BVars in U are collected in K.
       In particular, . ||- U means U contains no EVars or BVars.  Similarly,
       for spines K ||- S and other syntactic categories.

       Collection and abstraction raise Error if there are unresolved
       constraints after simplification.
    *)
  (* checkEmpty Cnstr = ()
       raises Error exception if constraints Cnstr cannot be simplified
       to the empty constraint
    *)
  (* eqEVar X Y = B
       where B iff X and Y represent same variable
    *)
  (* exists P K = B
       where B iff K = K1, Y, K2  s.t. P Y  holds
    *)
  (* occursInExp (k, U) = DP,

       Invariant:
       If    U in nf
       then  DP = No      iff k does not occur in U
             DP = Maybe   iff k occurs in U some place not as an argument to a Skonst
             DP = Meta    iff k occurs in U and only as arguments to Skonsts
    *)
  (* no case for Redex, EVar, EClo *)
  (* no case for FVar *)
  (* no case for SClo *)
  (* piDepend ((D,P), V) = Pi ((D,P'), V)
       where P' = Maybe if D occurs in V, P' = No otherwise
    *)
  (* optimize to have fewer traversals? -cs *)
  (* pre-Stelf 1.2 code walk Fri May  8 11:17:10 1998 *)
  (* weaken (depth,  G, a) = (w')
    *)
  (* raiseType (G, V) = {{G}} V

       Invariant:
       If G |- V : L
       then  . |- {{G}} V : L

       All abstractions are potentially dependent.
    *)
  (* collectExpW (tag_, d, G, (U, s), K) = K'

       Invariant:
       If    G |- s : G1     G1 |- U : V      (U,s) in whnf
       No circularities in U
             (enforced by extended occurs-check for BVars in Unify)
       and   K' = K, K''
             where K'' contains all EVars and BVars in (U,s)
    *)
  (* Possible optimization: Calculate also the normal form of the term *)
  (* optimization possible for d = 0 *)
  (* hack - should consult cs    -rv *)
  (* No other cases can occur due to whnf invariant *)
  (* collectExp (tag_, d, G, (U, s), K) = K'

       same as collectExpW  but  (U,s) need not to be in whnf
    *)
  (* collectSpine (tag_, d, G, (S, s), K) = K'

       Invariant:
       If    G |- s : G1     G1 |- S : V > P
       then  K' = K, K''
       where K'' contains all EVars and BVars in (S, s)
     *)
  (* collectDec (tag_, d, G, (x:V, s), K) = K'

       Invariant:
       If    G |- s : G1     G1 |- V : L
       then  K' = K, K''
       where K'' contains all EVars and BVars in (V, s)
    *)
  (* collectSub (tag_, d, G, s, K) = K'

       Invariant:
       If    G |- s : G1
       then  K' = K, K''
       where K'' contains all EVars and BVars in s
    *)
  (* abstractEVar (K, depth, X) = C'

       Invariant:
       If   G |- X : V
       and  |G| = depth
       and  X occurs in K  at kth position (starting at 1)
       then C' = BVar (depth + k)
       and  {{K}}, G |- C' : V
    *)
  (* lookupBV (A, i) = k'

       Invariant:

       If   A ||- V
       and  G |- V type
       and  G [x] A |- i : V'
       then ex a substititution  G x A |- s : G [x] A
       and  G x A |- k' : V''
       and  G x A |- V' [s] = V'' : type
    *)
  (* lookupBV' I.Null cannot occur by invariant *)
  (* abstractExpW (K, depth, (U, s)) = U'
       U' = {{U[s]}}_K

       Invariant:
       If    G |- s : G1     G1 |- U : V    (U,s) is in whnf
       and   K is internal context in dependency order
       and   |G| = depth
       and   K ||- U and K ||- V
       then  {{K}}, G |- U' : V'
       and   . ||- U' and . ||- V'
       and   U' is in nf
    *)
  (* s = id *)
  (* hack - should consult cs   -rv *)
  (* abstractExp (K, depth, (U, s)) = U'

       same as abstractExpW, but (U,s) need not to be in whnf
    *)
  (* abstractSub (K, depth, s, S) = S'      (implicit raising)
       S' = {{s}}_K @@ S

       Invariant:
       If   G |- s : G1
       and  |G| = depth
       and  K ||- s
       then {{K}}, G |- S' : {G1}.W > W   (for some W)
       and  . ||- S'
    *)
  (* n = 0 *)
  (* abstractSpine (K, depth, (S, s)) = S'
       where S' = {{S[s]}}_K

       Invariant:
       If   G |- s : G1     G1 |- S : V > P
       and  K ||- S
       and  |G| = depth

       then {{K}}, G |- S' : V' > P'
       and  . ||- S'
    *)
  (* abstractDec (K, depth, (x:V, s)) = x:V'
       where V = {{V[s]}}_K

       Invariant:
       If   G |- s : G1     G1 |- V : L
       and  K ||- V
       and  |G| = depth

       then {{K}}, G |- V' : L
       and  . ||- V'
    *)
  (* getlevel (V) = L if G |- V : L

       Invariant: G |- V : L' for some L'
    *)
  (* checkType (V) = () if G |- V : type

       Invariant: G |- V : L' for some L'
    *)
  (* abstractCtx (K, V) = V'
       where V' = {{K}} V

       Invariant:
       If   {{K}} |- V : L
       and  . ||- V

       then V' = {{K}} V
       and  . |- V' : L
       and  . ||- V'
    *)
  (* abstractGlobalSub (K, s, B) = s'

       Invariant:
       If   K > G   aux context
       and  G |- s : G'
       then K |- s' : G'
    *)
  (* collectGlobalSub (G0, s, B, collect) = collect'

       Invariant:
       If   |- G0 ctx
       and  |- G ctx
       and  G |- B tags
       and  G0 |- s : G
       and  collect is a function which maps
               (d, K)  (d expresses the number of parameters in K, |- K aux ctx)
            to K'      (|- K' aux ctx, which collects all EVars in K)
    *)
  (* no cases for (G0, s, B as I.Decl (_, S.Parameter NONE), collect) *)
  (* abstractNew ((G0, B0), s, B) = ((G', B'), s')

       Invariant:
       If   . |- G0 ctx
       and  G0 |- B0 tags
       and  G0 |- s : G
       and  G |- B tags
       then . |- G' = G1, Gp, G2
       and  G' |- B' tags
       and  G' |- s' : G
    *)
  (* abstractSub (t, B1, (G0, B0), s, B) = ((G', B'), s')

       Invariant:
       If   . |- t : G1
       and  G1 |- B1 tags

       and  G0 |- B0 tags
       and  G0 |- s : G
       and  G |- B tags
       then . |- G' = G1, G0, G2
       and  B' |- G' tags
       and  G' |- s' : G
    *)
  (* skip'' (K, (G, B)) = K'

             Invariant:
             If   G = x1:V1 .. xn:Vn
             and  G |- B = <param> ... <param> tags
             then  K' = K, BV (x1) .. BV (xn)
          *)
  (* abstractFor (K, depth, (F, s)) = F'
       F' = {{F[s]}}_K

       Invariant:
       If    G |- s : G1     G1 |- U : V    (U,s) is in whnf
       and   K is internal context in dependency order
       and   |G| = depth
       and   K ||- U and K ||- V
       then  {{K}}, G |- U' : V'
       and   . ||- U' and . ||- V'
       and   U' is in nf
    *)
  (* abstract (Gx, F) = F'

       Invariant:
       If   G, Gx |- F formula
       then G |- F' = {{Gx}} F formula
    *)
  (* shift G = s'

       Invariant:
       Forall contexts G0:
       If   |- G0, G ctx
       then G0, V, G |- s' : G0, G
    *)
  (* ctxSub (G, s) = G'

       Invariant:
       If   G2 |- s : G1
       and  G1 |- G ctx
       then G2 |- G' = G[s] ctx
    *)
  (* weaken2 (G, a, i, S) = w'

       Invariant:
       G |- w' : Gw
       Gw < G
       G |- S : {Gw} V > V
    *)
  (* raiseType (G, V) = {{G}} V

       Invariant:
       If G |- V : L
       then  . |- {{G}} V : L

       All abstractions are potentially dependent.
    *)
  (* raiseFor (G, F, w, sc) = F'

       Invariant:
       If   G0 |- G ctx
       and  G0, G, GF |- F for
       and  G0, {G} GF [...] |- w : G0
       and  sc maps  (G0, GA |- w : G0, |GA|)  to   (G0, GA, G[..] |- s : G0, G, GF)
       then G0, {G} GF |- F' for
    *)
  (* G0, {G}GF[..], G |- s : G0, G, GF *)
  (* G0, {G}GF[..], G |- V' : type *)
  (* G0, {G}GF[..], G |- nw : G0, {G}GF[..], Gw
                                         Gw < G *)
  (* G0, {G}GF[..], Gw |- iw : G0, {G}GF[..], G *)
  (* Generalize the invariant for Whnf.strengthen --cs *)
  (* G0, {G}GF[..], Gw |- V'' = V'[iw] : type*)
  (* G0, {G}GF[..] |- V''' = {Gw} V'' : type*)
  (* G0, {G}GF[..], G[..] |- S''' : {Gw} V''[..] > V''[..] *)
  (* G0, {G}GF[..], G |- s : G0, G, GF *)
  (* G0, GA |- w' : G0 *)
  (* G0, GA, G[..] |- s' : G0, G, GF *)
  (* G0, GA, G[..] |- (g+k'-k). S', s' : G0, G, GF, V *)
  (*                val G = F.listToCtx (ctxSub (F.ctxToList Gorig, w))
                  val g = I.ctxLength G
                  val s = sc (w, k)
                                         G0, {G}GF[..], G |- s : G0, G, GF 
                  val V' = Whnf.normalize (raiseType (G, Whnf.normalize (V, s)), I.id)
                                         G0, {G}GF[..] |- V' = {G}(V[s]) : type 
                  val S' = spine g
                                         G0, {G}GF[..] |- S' > {G}(V[s]) > V[s] 
                  val sc' = fn (w', k') =>
                              let
                                         G0, GA |- w' : G0 
                                val s' = sc (w', k')
                                         G0, GA, G[..] |- s' : G0, G, GF 
                              in
                                I.Dot (I.Exp (I.Root (I.BVar (g + k'-k), S')), s')
                                         G0, GA, G[..] |- g+k'-k. S', s' : G0, G, GF, V 
                              end
                  val F' = raiseFor (k+1, Gorig, F, I.comp (w, I.shift), sc')
                in
                  F.All (F.Prim (I.Dec (name, V')), F')
*)
  (* G0, {G}GF[..], G |- s : G0, G, GF *)
  (* G0, {G}GF[..], G |- V' : type *)
  (* G0, {G}GF[..], G |- nw : G0, {G}GF[..], Gw
                                         Gw < G *)
  (* G0, {G}GF[..], Gw |- iw : G0, {G}GF[..], G *)
  (* Generalize the invariant for Whnf.strengthen --cs *)
  (* G0, {G}GF[..], Gw |- V'' = V'[iw] : type*)
  (* G0, {G}GF[..] |- V''' = {Gw} V'' : type*)
  (* G0, {G}GF[..], G[..] |- S''' : {Gw} V''[..] > V''[..] *)
  (* G0, {G}GF[..], G |- s : G0, G, GF *)
  (* G0, GA |- w' : G0 *)
  (* G0, GA, G[..] |- s' : G0, G, GF *)
  (* G0, GA, G[..] |- (g+k'-k). S', s' : G0, G, GF, V *)
  (* the other case of F.All (F.Block _, _) is not yet covered *)
  (* makeFor (G, w, AF) = F'

       Invariant :
       If   |- G ctx
       and  G |- w : G'
       and  G' |- AF approx for
       then G'; . |- F' = {EVARS} AF  for
    *)
  (*        val _ = if !Global.doubleCheck then checkTags (GK, BK) else () *)
  (* BUG *)
  let weaken = weaken
  let raiseType = raiseType
  let abstractSub = abstractSubAll
  let abstractSub' a b c = abstractNew (a, b, c)
  let abstractApproxFor = abstractApproxFor
end
(*! sharing Abstract.IntSyn = IntSyn' !*)
(* functor MTPAbstract *)

(* # 1 "src/meta/MtpAbstract.sml.ml" *)
