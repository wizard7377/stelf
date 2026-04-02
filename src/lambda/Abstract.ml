(* # 1 "src/lambda/Abstract.sig.ml" *)
open! Basis
open Intsyn
open Tomega

(* Abstraction *)
(* Author: Frank Pfenning, Carsten Schuermann *)
include Abstract_intf
(* signature ABSTRACT *)

(* # 1 "src/lambda/Abstract.fun.ml" *)
open! Whnf
open! Unify
open! Constraints
open! Basis
open Intsyn
open Tomega

(* Abstraction *)
(* Author: Frank Pfenning, Carsten Schuermann *)
(* Modified: Roberto Virga *)
module MakeAbstract
    (Whnf : WHNF)
    (Unify : UNIFY)
    (Constraints : CONSTRAINTS) :
  ABSTRACT = struct
  exception Error of string

  open! struct
    module I = IntSyn
    module T = Tomega
    module C = Constraints
    module O = Order

    type eFLVar =
      | Ev of I.exp
      | Fv of string * I.exp
      | Lv of I.block
      | Pv of T.prg

    let rec collectConstraints = function
      | I.Null -> []
      | I.Decl (g_, Fv _) -> collectConstraints g_
      | I.Decl (g_, Ev (I.EVar (_, _, _, { contents = [] }))) ->
          collectConstraints g_
      | I.Decl (g_, Ev (I.EVar (_, _, _, { contents = cnstrL }))) ->
          C.simplify cnstrL @ collectConstraints g_
      | I.Decl (g_, Lv _) -> collectConstraints g_

    let rec checkConstraints k_ =
      let constraints = collectConstraints k_ in
      let _ =
        begin match constraints with
        | [] -> ()
        | _ -> raise (C.Error constraints)
        end
      in
      ()

    let rec eqEVar arg__1 arg__2 =
      begin match (arg__1, arg__2) with
      | I.EVar (r1, _, _, _), Ev (I.EVar (r2, _, _, _)) -> r1 == r2
      | _, _ -> false
      end

    let rec eqFVar arg__3 arg__4 =
      begin match (arg__3, arg__4) with
      | I.FVar (n1, _, _), Fv (n2, _) -> n1 = n2
      | _, _ -> false
      end

    let rec eqLVar arg__5 arg__6 =
      begin match (arg__5, arg__6) with
      | I.LVar (r1, _, _), Lv (I.LVar (r2, _, _)) -> r1 == r2
      | _, _ -> false
      end

    let rec exists p_ k_ =
      let rec exists' = function
        | I.Null -> false
        | I.Decl (k'_, y_) -> p_ y_ || exists' k'_
      in
      exists' k_

    let rec ( or ) = function
      | I.Maybe, _ -> I.Maybe
      | _, I.Maybe -> I.Maybe
      | I.Meta, _ -> I.Meta
      | _, I.Meta -> I.Meta
      | I.No, I.No -> I.No

    let rec occursInExp = function
      | k, I.Uni _ -> I.No
      | k, I.Pi (dp_, v_) ->
          ( or ) (occursInDecP (k, dp_), occursInExp (k + 1, v_))
      | k, I.Root (h_, s_) -> occursInHead (k, h_, occursInSpine (k, s_))
      | k, I.Lam (d_, v_) ->
          ( or ) (occursInDec (k, d_), occursInExp (k + 1, v_))
      | k, I.FgnExp (csfe_csid, csfe_ops) ->
          I.FgnExpStd.fold (csfe_csid, csfe_ops)
            (function
              | u_, dp_ ->
                  ( or ) (dp_, occursInExp (k, Whnf.normalize (u_, I.id))))
            I.No

    and occursInHead = function
      | k, I.BVar k', dp_ -> begin if k = k' then I.Maybe else dp_ end
      | k, I.Const _, dp_ -> dp_
      | k, I.Def _, dp_ -> dp_
      | k, I.Proj _, dp_ -> dp_
      | k, I.FgnConst _, dp_ -> dp_
      | k, I.Skonst _, I.No -> I.No
      | k, I.Skonst _, I.Meta -> I.Meta
      | k, I.Skonst _, I.Maybe -> I.Meta

    and occursInSpine = function
      | _, I.Nil -> I.No
      | k, I.App (u_, s_) -> ( or ) (occursInExp (k, u_), occursInSpine (k, s_))

    and occursInDec (k, I.Dec (_, v_)) = occursInExp (k, v_)
    and occursInDecP (k, (d_, _)) = occursInDec (k, d_)

    let rec piDepend = function
      | (d_, I.No), v_ -> I.Pi ((d_, I.No), v_)
      | (d_, I.Meta), v_ -> I.Pi ((d_, I.Meta), v_)
      | (d_, I.Maybe), v_ -> I.Pi ((d_, occursInExp (1, v_)), v_)

    let rec raiseType = function
      | I.Null, v_ -> v_
      | I.Decl (g_, d_), v_ -> raiseType (g_, I.Pi ((d_, I.Maybe), v_))

    let rec raiseTerm = function
      | I.Null, u_ -> u_
      | I.Decl (g_, d_), u_ -> raiseTerm (g_, I.Lam (d_, u_))

    let rec collectExpW = function
      | g_, (I.Uni l_, s), k_ -> k_
      | g_, (I.Pi ((d_, _), v_), s), k_ ->
          collectExp
            ( I.Decl (g_, I.decSub (d_, s)),
              (v_, I.dot1 s),
              collectDec (g_, (d_, s), k_) )
      | g_, (I.Root ((I.FVar (name, v_, s') as f_), s_), s), k_ -> begin
          if exists (eqFVar f_) k_ then collectSpine (g_, (s_, s), k_)
          else
            collectSpine
              ( g_,
                (s_, s),
                I.Decl (collectExp (I.Null, (v_, I.id), k_), Fv (name, v_)) )
        end
      | ( g_,
          ( I.Root
              (I.Proj ((I.LVar ({ contents = None }, sk, (l, t)) as l_), i), s_),
            s ),
          k_ ) ->
          collectSpine (g_, (s_, s), collectBlock (g_, I.blockSub (l_, s), k_))
      | g_, (I.Root (_, s_), s), k_ -> collectSpine (g_, (s_, s), k_)
      | g_, (I.Lam (d_, u_), s), k_ ->
          collectExp
            ( I.Decl (g_, I.decSub (d_, s)),
              (u_, I.dot1 s),
              collectDec (g_, (d_, s), k_) )
      | g_, ((I.EVar (r, gx_, v_, cnstrs) as x_), s), k_ -> begin
          if exists (eqEVar x_) k_ then collectSub (g_, s, k_)
          else
            let v'_ = raiseType (gx_, v_) in
            let k'_ = collectExp (I.Null, (v'_, I.id), k_) in
            collectSub (g_, s, I.Decl (k'_, Ev x_))
        end
      | g_, (I.FgnExp (csfe_csid, csfe_ops), s), k_ ->
          I.FgnExpStd.fold (csfe_csid, csfe_ops)
            (function u_, k_ -> collectExp (g_, (u_, s), k_))
            k_

    and collectExp (g_, us_, k_) = collectExpW (g_, Whnf.whnf us_, k_)

    and collectSpine = function
      | g_, (I.Nil, _), k_ -> k_
      | g_, (I.SClo (s_, s'), s), k_ ->
          collectSpine (g_, (s_, I.comp (s', s)), k_)
      | g_, (I.App (u_, s_), s), k_ ->
          collectSpine (g_, (s_, s), collectExp (g_, (u_, s), k_))

    and collectDec = function
      | g_, (I.Dec (_, v_), s), k_ -> collectExp (g_, (v_, s), k_)
      | g_, (I.BDec (_, (_, t)), s), k_ -> collectSub (g_, I.comp (t, s), k_)
      | g_, (I.NDec _, s), k_ -> k_

    and collectSub = function
      | g_, I.Shift _, k_ -> k_
      | g_, I.Dot (I.Idx _, s), k_ -> collectSub (g_, s, k_)
      | g_, I.Dot (I.Exp u_, s), k_ ->
          collectSub (g_, s, collectExp (g_, (u_, I.id), k_))
      | g_, I.Dot (I.Block b_, s), k_ ->
          collectSub (g_, s, collectBlock (g_, b_, k_))

    and collectBlock = function
      | g_, I.LVar ({ contents = Some b_ }, sk, _), k_ ->
          collectBlock (g_, I.blockSub (b_, sk), k_)
      | g_, (I.LVar (_, sk, (l, t)) as l_), k_ -> begin
          if exists (eqLVar l_) k_ then collectSub (g_, I.comp (t, sk), k_)
          else I.Decl (collectSub (g_, I.comp (t, sk), k_), Lv l_)
        end

    let rec collectCtx = function
      | g0_, I.Null, k_ -> (g0_, k_)
      | g0_, I.Decl (g_, d_), k_ ->
          let g0'_, k'_ = collectCtx (g0_, g_, k_) in
          let k''_ = collectDec (g0'_, (d_, I.id), k'_) in
          (I.Decl (g0_, d_), k''_)

    let rec collectCtxs = function
      | g0_, [], k_ -> k_
      | g0_, g_ :: gs_, k_ ->
          let g0'_, k'_ = collectCtx (g0_, g_, k_) in
          collectCtxs (g0'_, gs_, k'_)

    let rec abstractEVar = function
      | ( I.Decl (k'_, Ev (I.EVar (r', _, _, _))),
          depth,
          (I.EVar (r, _, _, _) as x_) ) -> begin
          if r == r' then I.BVar (depth + 1)
          else abstractEVar (k'_, depth + 1, x_)
        end
      | I.Decl (k'_, _), depth, x_ -> abstractEVar (k'_, depth + 1, x_)

    let rec abstractFVar = function
      | I.Decl (k'_, Fv (n', _)), depth, (I.FVar (n, _, _) as f_) -> begin
          if n = n' then I.BVar (depth + 1)
          else abstractFVar (k'_, depth + 1, f_)
        end
      | I.Decl (k'_, _), depth, f_ -> abstractFVar (k'_, depth + 1, f_)

    let rec abstractLVar = function
      | I.Decl (k'_, Lv (I.LVar (r', _, _))), depth, (I.LVar (r, _, _) as l_) ->
        begin
          if r == r' then I.Bidx (depth + 1)
          else abstractLVar (k'_, depth + 1, l_)
        end
      | I.Decl (k'_, _), depth, l_ -> abstractLVar (k'_, depth + 1, l_)

    let rec abstractExpW = function
      | k_, depth, ((I.Uni l_ as u_), s) -> u_
      | k_, depth, (I.Pi ((d_, p_), v_), s) ->
          piDepend
            ( (abstractDec (k_, depth, (d_, s)), p_),
              abstractExp (k_, depth + 1, (v_, I.dot1 s)) )
      | k_, depth, (I.Root ((I.FVar _ as f_), s_), s) ->
          I.Root
            (abstractFVar (k_, depth, f_), abstractSpine (k_, depth, (s_, s)))
      | k_, depth, (I.Root (I.Proj ((I.LVar _ as l_), i), s_), s) ->
          I.Root
            ( I.Proj (abstractLVar (k_, depth, l_), i),
              abstractSpine (k_, depth, (s_, s)) )
      | k_, depth, (I.Root (h_, s_), s) ->
          I.Root (h_, abstractSpine (k_, depth, (s_, s)))
      | k_, depth, (I.Lam (d_, u_), s) ->
          I.Lam
            ( abstractDec (k_, depth, (d_, s)),
              abstractExp (k_, depth + 1, (u_, I.dot1 s)) )
      | k_, depth, ((I.EVar _ as x_), s) ->
          I.Root
            (abstractEVar (k_, depth, x_), abstractSub (k_, depth, s, I.Nil))
      | k_, depth, (I.FgnExp (csfe_csid, csfe_ops), s) ->
          I.FgnExpStd.Map.apply (csfe_csid, csfe_ops) (function u_ ->
              abstractExp (k_, depth, (u_, s)))

    and abstractExp (k_, depth, us_) = abstractExpW (k_, depth, Whnf.whnf us_)

    and abstractSub = function
      | k_, depth, I.Shift k, s_ -> begin
          if k < depth then
            abstractSub (k_, depth, I.Dot (I.Idx (k + 1), I.Shift (k + 1)), s_)
          else s_
        end
      | k_, depth, I.Dot (I.Idx k, s), s_ ->
          abstractSub (k_, depth, s, I.App (I.Root (I.BVar k, I.Nil), s_))
      | k_, depth, I.Dot (I.Exp u_, s), s_ ->
          abstractSub
            (k_, depth, s, I.App (abstractExp (k_, depth, (u_, I.id)), s_))

    and abstractSpine = function
      | k_, depth, (I.Nil, _) -> I.Nil
      | k_, depth, (I.SClo (s_, s'), s) ->
          abstractSpine (k_, depth, (s_, I.comp (s', s)))
      | k_, depth, (I.App (u_, s_), s) ->
          I.App
            ( abstractExp (k_, depth, (u_, s)),
              abstractSpine (k_, depth, (s_, s)) )

    and abstractDec (k_, depth, (I.Dec (x, v_), s)) =
      I.Dec (x, abstractExp (k_, depth, (v_, s)))

    let rec abstractSOME = function
      | k_, I.Shift 0 -> I.Shift (I.ctxLength k_)
      | k_, I.Shift n -> I.Shift (I.ctxLength k_)
      | k_, I.Dot (I.Idx k, s) -> I.Dot (I.Idx k, abstractSOME (k_, s))
      | k_, I.Dot (I.Exp u_, s) ->
          I.Dot (I.Exp (abstractExp (k_, 0, (u_, I.id))), abstractSOME (k_, s))
      | k_, I.Dot (I.Block (I.LVar _ as l_), s) ->
          I.Dot (I.Block (abstractLVar (k_, 0, l_)), abstractSOME (k_, s))

    let rec abstractCtx = function
      | k_, depth, I.Null -> (I.Null, depth)
      | k_, depth, I.Decl (g_, d_) ->
          let g'_, depth' = abstractCtx (k_, depth, g_) in
          let d'_ = abstractDec (k_, depth', (d_, I.id)) in
          (I.Decl (g'_, d'_), depth' + 1)

    let rec abstractCtxlist = function
      | k_, depth, [] -> []
      | k_, depth, g_ :: gs_ ->
          let g'_, depth' = abstractCtx (k_, depth, g_) in
          let gs'_ = abstractCtxlist (k_, depth', gs_) in
          g'_ :: gs'_

    let rec abstractKPi = function
      | I.Null, v_ -> v_
      | I.Decl (k'_, Ev (I.EVar (_, gx_, vx_, _))), v_ ->
          let v'_ = raiseType (gx_, vx_) in
          let v''_ = abstractExp (k'_, 0, (v'_, I.id)) in
          abstractKPi (k'_, I.Pi ((I.Dec (None, v''_), I.Maybe), v_))
      | I.Decl (k'_, Fv (name, v'_)), v_ ->
          let v''_ = abstractExp (k'_, 0, (v'_, I.id)) in
          abstractKPi (k'_, I.Pi ((I.Dec (Some name, v''_), I.Maybe), v_))
      | I.Decl (k'_, Lv (I.LVar (r, _, (l, t)))), v_ ->
          let t' = abstractSOME (k'_, t) in
          abstractKPi (k'_, I.Pi ((I.BDec (None, (l, t')), I.Maybe), v_))

    let rec abstractKLam = function
      | I.Null, u_ -> u_
      | I.Decl (k'_, Ev (I.EVar (_, gx_, vx_, _))), u_ ->
          let v'_ = raiseType (gx_, vx_) in
          abstractKLam
            (k'_, I.Lam (I.Dec (None, abstractExp (k'_, 0, (v'_, I.id))), u_))
      | I.Decl (k'_, Fv (name, v'_)), u_ ->
          abstractKLam
            ( k'_,
              I.Lam (I.Dec (Some name, abstractExp (k'_, 0, (v'_, I.id))), u_)
            )

    let rec abstractKCtx = function
      | I.Null -> I.Null
      | I.Decl (k'_, Ev (I.EVar (_, gx_, vx_, _))) ->
          let v'_ = raiseType (gx_, vx_) in
          let v''_ = abstractExp (k'_, 0, (v'_, I.id)) in
          I.Decl (abstractKCtx k'_, I.Dec (None, v''_))
      | I.Decl (k'_, Fv (name, v'_)) ->
          let v''_ = abstractExp (k'_, 0, (v'_, I.id)) in
          I.Decl (abstractKCtx k'_, I.Dec (Some name, v''_))
      | I.Decl (k'_, Lv (I.LVar (r, _, (l, t)))) ->
          let t' = abstractSOME (k'_, t) in
          I.Decl (abstractKCtx k'_, I.BDec (None, (l, t')))

    let rec abstractDecImp v_ =
      let k_ = collectExp (I.Null, (v_, I.id), I.Null) in
      let _ = checkConstraints k_ in
      (I.ctxLength k_, abstractKPi (k_, abstractExp (k_, 0, (v_, I.id))))

    let rec abstractDef (u_, v_) =
      let k_ =
        collectExp (I.Null, (u_, I.id), collectExp (I.Null, (v_, I.id), I.Null))
      in
      let _ = checkConstraints k_ in
      ( I.ctxLength k_,
        ( abstractKLam (k_, abstractExp (k_, 0, (u_, I.id))),
          abstractKPi (k_, abstractExp (k_, 0, (v_, I.id))) ) )

    let rec abstractSpineExt (s_, s) =
      let k_ = collectSpine (I.Null, (s_, s), I.Null) in
      let _ = checkConstraints k_ in
      let g_ = abstractKCtx k_ in
      let s_ = abstractSpine (k_, 0, (s_, s)) in
      (g_, s_)

    let rec abstractCtxs gs_ =
      let k_ = collectCtxs (I.Null, gs_, I.Null) in
      let _ = checkConstraints k_ in
      (abstractKCtx k_, abstractCtxlist (k_, 0, gs_))

    let rec closedDec (g_, (I.Dec (_, v_), s)) =
      begin match collectExp (g_, (v_, s), I.Null) with
      | I.Null -> true
      | _ -> false
      end

    let rec closedSub = function
      | g_, I.Shift _ -> true
      | g_, I.Dot (I.Idx _, s) -> closedSub (g_, s)
      | g_, I.Dot (I.Exp u_, s) -> begin
          match collectExp (g_, (u_, I.id), I.Null) with
          | I.Null -> closedSub (g_, s)
          | _ -> false
        end

    let rec closedExp (g_, (u_, s)) =
      begin match collectExp (g_, (u_, I.id), I.Null) with
      | I.Null -> true
      | _ -> false
      end

    let rec closedCtx = function
      | I.Null -> true
      | I.Decl (g_, d_) -> closedCtx g_ && closedDec (g_, (d_, I.id))

    let rec closedFor = function
      | psi_, True -> true
      | psi_, T.All ((d_, _), f_) ->
          closedDEC (psi_, d_) && closedFor (I.Decl (psi_, d_), f_)
      | psi_, T.Ex ((d_, _), f_) ->
          closedDec (T.coerceCtx psi_, (d_, I.id))
          && closedFor (I.Decl (psi_, T.UDec d_), f_)

    and closedDEC = function
      | psi_, T.UDec d_ -> closedDec (T.coerceCtx psi_, (d_, I.id))
      | psi_, T.PDec (_, f_, _, _) -> closedFor (psi_, f_)

    let rec closedCTX = function
      | I.Null -> true
      | I.Decl (psi_, d_) -> closedCTX psi_ && closedDEC (psi_, d_)

    let rec evarsToK = function
      | [] -> I.Null
      | x_ :: xs_ -> I.Decl (evarsToK xs_, Ev x_)

    let rec kToEVars_ = function
      | I.Null -> []
      | I.Decl (k_, Ev x_) -> x_ :: kToEVars_ k_
      | I.Decl (k_, _) -> kToEVars_ k_

    let rec collectEVars (g_, us_, xs_) =
      kToEVars_ (collectExp (g_, us_, evarsToK xs_))

    let rec collectEVarsSpine (g_, (s_, s), xs_) =
      kToEVars_ (collectSpine (g_, (s_, s), evarsToK xs_))

    let rec collectPrg = function
      | _, (T.EVar (psi_, r, f_, _, _, _) as p_), k_ -> I.Decl (k_, Pv p_)
      | psi_, Unit, k_ -> k_
      | psi_, T.PairExp (u_, p_), k_ ->
          collectPrg (psi_, p_, collectExp (T.coerceCtx psi_, (u_, I.id), k_))

    let rec abstractPVar = function
      | ( I.Decl (k'_, Pv (T.EVar (_, r', _, _, _, _))),
          depth,
          (T.EVar (_, r, _, _, _, _) as p_) ) -> begin
          if r == r' then T.Var (depth + 1)
          else abstractPVar (k'_, depth + 1, p_)
        end
      | I.Decl (k'_, _), depth, p_ -> abstractPVar (k'_, depth + 1, p_)

    let rec abstractPrg = function
      | k_, depth, (T.EVar _ as x_) -> abstractPVar (k_, depth, x_)
      | k_, depth, T.Unit -> T.Unit
      | k_, depth, T.PairExp (u_, p_) ->
          T.PairExp
            (abstractExp (k_, depth, (u_, I.id)), abstractPrg (k_, depth, p_))

    let rec collectTomegaSub = function
      | T.Shift 0 -> I.Null
      | T.Dot (T.Exp u_, t) ->
          collectExp (I.Null, (u_, I.id), collectTomegaSub t)
      | T.Dot (T.Block b_, t) -> collectBlock (I.Null, b_, collectTomegaSub t)
      | T.Dot (T.Prg p_, t) -> collectPrg (I.Null, p_, collectTomegaSub t)

    let rec abstractOrder = function
      | k_, depth, O.Arg (us1_, us2_) ->
          O.Arg
            ( (abstractExp (k_, depth, us1_), I.id),
              (abstractExp (k_, depth, us2_), I.id) )
      | k_, depth, O.Simul os_ ->
          O.Simul (map (function o_ -> abstractOrder (k_, depth, o_)) os_)
      | k_, depth, O.Lex os_ ->
          O.Lex (map (function o_ -> abstractOrder (k_, depth, o_)) os_)

    let rec abstractTC = function
      | k_, depth, T.Abs (d_, tc_) ->
          T.Abs
            (abstractDec (k_, depth, (d_, I.id)), abstractTC (k_, depth, tc_))
      | k_, depth, T.Conj (tc1_, tc2_) ->
          T.Conj (abstractTC (k_, depth, tc1_), abstractTC (k_, depth, tc2_))
      | k_, depth, T.Base o_ -> T.Base (abstractOrder (k_, depth, o_))

    let rec abstractTCOpt = function
      | k_, depth, None -> None
      | k_, depth, Some tc_ -> Some (abstractTC (k_, depth, tc_))

    let rec abstractMetaDec = function
      | k_, depth, T.UDec d_ -> T.UDec (abstractDec (k_, depth, (d_, I.id)))
      | k_, depth, T.PDec (xx, f_, tc1_, tc2_) ->
          T.PDec (xx, abstractFor (k_, depth, f_), tc1_, tc2_)

    and abstractFor = function
      | k_, depth, T.True -> T.True
      | k_, depth, T.All ((md_, q_), f_) ->
          T.All
            ((abstractMetaDec (k_, depth, md_), q_), abstractFor (k_, depth, f_))
      | k_, depth, T.Ex ((d_, q_), f_) ->
          T.Ex
            ( (abstractDec (k_, depth, (d_, I.id)), q_),
              abstractFor (k_, depth, f_) )
      | k_, depth, T.And (f1_, f2_) ->
          T.And (abstractFor (k_, depth, f1_), abstractFor (k_, depth, f2_))
      | k_, depth, T.World (w_, f_) -> T.World (w_, abstractFor (k_, depth, f_))

    let rec abstractPsi = function
      | I.Null -> I.Null
      | I.Decl (k'_, Ev (I.EVar (_, gx_, vx_, _))) ->
          let v'_ = raiseType (gx_, vx_) in
          let v''_ = abstractExp (k'_, 0, (v'_, I.id)) in
          I.Decl (abstractPsi k'_, T.UDec (I.Dec (None, v''_)))
      | I.Decl (k'_, Fv (name, v'_)) ->
          let v''_ = abstractExp (k'_, 0, (v'_, I.id)) in
          I.Decl (abstractPsi k'_, T.UDec (I.Dec (Some name, v''_)))
      | I.Decl (k'_, Lv (I.LVar (r, _, (l, t)))) ->
          let t' = abstractSOME (k'_, t) in
          I.Decl (abstractPsi k'_, T.UDec (I.BDec (None, (l, t'))))
      | I.Decl (k'_, Pv (T.EVar (gx_, _, fx_, tc1_, tc2_, _))) ->
          let f'_ = abstractFor (k'_, 0, T.forSub (fx_, T.id)) in
          let tc1'_ = abstractTCOpt (k'_, 0, tc1_) in
          let tc2'_ = abstractTCOpt (k'_, 0, tc2_) in
          I.Decl (abstractPsi k'_, T.PDec (None, f'_, tc1_, tc2_))

    let rec abstractTomegaSub t =
      let k_ = collectTomegaSub t in
      let t' = abstractTomegaSub' (k_, 0, t) in
      let psi_ = abstractPsi k_ in
      (psi_, t')

    and abstractTomegaSub' = function
      | k_, depth, T.Shift 0 -> T.Shift depth
      | k_, depth, T.Dot (T.Exp u_, t) ->
          T.Dot
            ( T.Exp (abstractExp (k_, depth, (u_, I.id))),
              abstractTomegaSub' (k_, depth, t) )
      | k_, depth, T.Dot (T.Block b_, t) ->
          T.Dot
            ( T.Block (abstractLVar (k_, depth, b_)),
              abstractTomegaSub' (k_, depth, t) )
      | k_, depth, T.Dot (T.Prg p_, t) ->
          T.Dot
            ( T.Prg (abstractPrg (k_, depth, p_)),
              abstractTomegaSub' (k_, depth, t) )

    let rec abstractTomegaPrg p_ =
      let k_ = collectPrg (I.Null, p_, I.Null) in
      let p'_ = abstractPrg (k_, 0, p_) in
      let psi_ = abstractPsi k_ in
      (psi_, p'_)
  end

  (* Intermediate Data Structure *)
  (* Y ::= X         for  GX |- X : VX *)
  (*     | (F, V)        if . |- F : V *)
  (*     | L             if . |- L in W *)
  (*     | P                            *)
  (*
       We write {{K}} for the context of K, where EVars, FVars, LVars have
       been translated to declarations and their occurrences to BVars.
       We write {{U}}_K, {{S}}_K for the corresponding translation of an
       expression or spine.

       Just like contexts G, any K is implicitly assumed to be
       well-formed and in dependency Order.

       We write  K ||- U  if all EVars and FVars in U are collected in K.
       In particular, . ||- U means U contains no EVars or FVars.  Similarly,
       for spines K ||- S and other syntactic categories.

       Collection and abstraction raise Error if there are unresolved
       constraints after simplification.
    *)
  (* collectConstraints K = cnstrs
       where cnstrs collects all constraints attached to EVars in K
    *)
  (* checkConstraints (K) = ()
       Effect: raises Constraints.Error(C) if K contains unresolved constraints
    *)
  (* checkEmpty Cnstr = ()
       raises Error exception if constraints Cnstr cannot be simplified
       to the empty constraint
    *)
  (*
    fun checkEmpty (nil) = ()
      | checkEmpty (Cnstr) =
        (case C.simplify Cnstr
           of nil => ()
            | _ => raise Error ""Typing ambiguous -- unresolved constraints"")
    *)
  (* eqEVar X Y = B
       where B iff X and Y represent same variable
    *)
  (* eqFVar F Y = B
       where B iff X and Y represent same variable
    *)
  (* eqLVar L Y = B
       where B iff X and Y represent same variable
    *)
  (* exists P K = B
       where B iff K = K1, Y, K2  s.t. P Y  holds
    *)
  (* this should be non-strict *)
  (* perhaps the whole repeated traversal are now a performance
       bottleneck in PCC applications where logic programming search
       followed by abstraction creates certificates.  such certificates
       are large, so the quadratic algorithm is not really acceptable.
       possible improvement, collect, abstract, then traverse one more
       time to determine status of all variables.
    *)
  (* Wed Aug  6 16:37:57 2003 -fp *)
  (* !!! *)
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
  (* raiseType (G, V) = {{G}} V

       Invariant:
       If G |- V : L
       then  . |- {{G}} V : L

       All abstractions are potentially dependent.
    *)
  (* raiseTerm (G, U) = [[G]] U

       Invariant:
       If G |- U : V
       then  . |- [[G]] U : {{G}} V

       All abstractions are potentially dependent.
    *)
  (* collectExpW (G, (U, s), K) = K'

       Invariant:
       If    G |- s : G1     G1 |- U : V      (U,s) in whnf
       No circularities in U
             (enforced by extended occurs-check for FVars in Unify)
       and   K' = K, K''
             where K'' contains all EVars and FVars in (U,s)
    *)
  (* Possible optimization: Calculate also the normal form of the term *)
  (* s' = ^|G| *)
  (* BUG : We forget to deref L.  use collectBlock instead
             FPCHECK
             -cs Sat Jul 24 18:48:59 2010
            was:
      | collectExpW (G, (I.Root (I.Proj (L as I.LVar (r, sk, (l, t)), i), S), s), K) =
        if exists (eqLVar L) K
           note: don't collect t again below 
           was: collectSpine (G, (S, s), collectSub (I.Null, t, K)) 
           Sun Dec 16 10:54:52 2001 -fp !!! 
          then collectSpine (G, (S, s), K)
        else
           -fp Sun Dec  1 21:12:12 2002 
         collectSpine (G, (S, s), I.Decl (collectSub (G, I.comp(t,s), K), LV L)) 
         was :
         collectSpine (G, (S, s), collectSub (G, I.comp(t,s), I.Decl (K, LV L)))
         July 22, 2010 -fp -cs
         
            collectSpine (G, (S, s), collectSub (G, I.comp(t,I.comp(sk,s)),
                                                 I.Decl (K, LV L)))
*)
  (* val _ = checkEmpty !cnstrs *)
  (* inefficient *)
  (* No other cases can occur due to whnf invariant *)
  (* collectExp (G, (U, s), K) = K'

       same as collectExpW  but  (U,s) need not to be in whnf
    *)
  (* collectSpine (G, (S, s), K) = K'

       Invariant:
       If    G |- s : G1     G1 |- S : V > P
       then  K' = K, K''
       where K'' contains all EVars and FVars in (S, s)
     *)
  (* collectDec (G, (x:V, s), K) = K'

       Invariant:
       If    G |- s : G1     G1 |- V : L
       then  K' = K, K''
       where K'' contains all EVars and FVars in (V, s)
    *)
  (* . |- t : Gsome, so do not compose with s *)
  (* Sat Dec  8 13:28:15 2001 -fp *)
  (* was: collectSub (I.Null, t, K) *)
  (* collectSub (G, s, K) = K'

       Invariant:
       If    G |- s : G1
       then  K' = K, K''
       where K'' contains all EVars and FVars in s
    *)
  (* next case should be impossible *)
  (*
      | collectSub (G, I.Dot (I.Undef, s), K) =
          collectSub (G, s, K)
    *)
  (* collectBlock (G, B, K) where G |- B block *)
  (* collectBlock (B, K) *)
  (* correct?? -fp Sun Dec  1 21:15:33 2002 *)
  (* was: t in the two lines above, July 22, 2010, -fp -cs *)
  (* | collectBlock (G, I.Bidx _, K) = K *)
  (* should be impossible: Fronts of substitutions are never Bidx *)
  (* Sat Dec  8 13:30:43 2001 -fp *)
  (* collectCtx (G0, G, K) = (G0', K')
       Invariant:
       If G0 |- G ctx,
       then G0' = G0,G
       and K' = K, K'' where K'' contains all EVars and FVars in G
    *)
  (* collectCtxs (G0, Gs, K) = K'
       Invariant: G0 |- G1,...,Gn ctx where Gs = [G1,...,Gn]
       and K' = K, K'' where K'' contains all EVars and FVars in G1,...,Gn
    *)
  (* abstractEVar (K, depth, X) = C'

       Invariant:
       If   G |- X : V
       and  |G| = depth
       and  X occurs in K  at kth position (starting at 1)
       then C' = BVar (depth + k)
       and  {{K}}, G |- C' : V
    *)
  (*      | abstractEVar (I.Decl (K', FV (n', _)), depth, X) =
          abstractEVar (K', depth+1, X) remove later --cs*)
  (* abstractFVar (K, depth, F) = C'

       Invariant:
       If   G |- F : V
       and  |G| = depth
       and  F occurs in K  at kth position (starting at 1)
       then C' = BVar (depth + k)
       and  {{K}}, G |- C' : V
    *)
  (*      | abstractFVar (I.Decl(K', EV _), depth, F) =
          abstractFVar (K', depth+1, F) remove later --cs *)
  (* abstractLVar (K, depth, L) = C'

       Invariant:
       If   G |- L : V
       and  |G| = depth
       and  L occurs in K  at kth position (starting at 1)
       then C' = Bidx (depth + k)
       and  {{K}}, G |- C' : V
    *)
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
  (* k = depth *)
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
  (* abstractSOME (K, s) = s'
       s' = {{s}}_K

       Invariant:
       If    . |- s : Gsome
       and   K is internal context in dependency order
       and   K ||- s
       then  {{K}} |- s' : Gsome  --- not changing domain of s'

       Update: modified for globality invariant of . |- t : Gsome
       Sat Dec  8 13:35:55 2001 -fp
       Above is now incorrect
       Sun Dec  1 22:36:50 2002 -fp
    *)
  (* n = 0 by invariant, check for now *)
  (* n > 0 *)
  (* I.Block (I.Bidx _) should be impossible as head of substitutions *)
  (* abstractCtx (K, depth, G) = (G', depth')
       where G' = {{G}}_K

       Invariants:
       If G0 |- G ctx
       and K ||- G
       and |G0| = depth
       then {{K}}, G0 |- G' ctx
       and . ||- G'
       and |G0,G| = depth'
    *)
  (* abstractCtxlist (K, depth, [G1,...,Gn]) = [G1',...,Gn']
       where Gi' = {{Gi}}_K

       Invariants:
       if G0 |- G1,...,Gn ctx
       and K ||- G1,...,Gn
       and |G0| = depth
       then {{K}}, G0 |- G1',...,Gn' ctx
       and . ||- G1',...,Gn'
    *)
  (* dead code under new reconstruction -kw
     getlevel (V) = L if G |- V : L

       Invariant: G |- V : L' for some L'
    
    fun getLevel (I.Uni _) = I.Kind
      | getLevel (I.Pi (_, U)) = getLevel U
      | getLevel (I.Root _)  = I.Type
      | getLevel (I.Redex (U, _)) = getLevel U
      | getLevel (I.Lam (_, U)) = getLevel U
      | getLevel (I.EClo (U,_)) = getLevel U

     checkType (V) = () if G |- V : type

       Invariant: G |- V : L' for some L'
    
    fun checkType V =
        (case getLevel V
           of I.Type => ()
            | _ => raise Error ""Typing ambiguous -- free type variable"")
    *)
  (* abstractKPi (K, V) = V'
       where V' = {{K}} V

       Invariant:
       If   {{K}} |- V : L
       and  . ||- V

       then V' = {{K}} V
       and  . |- V' : L
       and  . ||- V'
    *)
  (* enforced by reconstruction -kw
          val _ = checkType V'' *)
  (* enforced by reconstruction -kw
          val _ = checkType V'' *)
  (* abstractKLam (K, U) = U'
       where U' = [[K]] U

       Invariant:
       If   {{K}} |- U : V
       and  . ||- U
       and  . ||- V

       then U' = [[K]] U
       and  . |- U' : {{K}} V
       and  . ||- U'
    *)
  (* enforced by reconstruction -kw
          val _ = checkType V'' *)
  (* enforced by reconstruction -kw
          val _ = checkType V'' *)
  (* abstractDecImp V = (k', V')    rename --cs  (see above) 

       Invariant:
       If    . |- V : L
       and   K ||- V

       then  . |- V' : L
       and   V' = {{K}} V
       and   . ||- V'
       and   k' = |K|
    *)
  (* abstractDef  (U, V) = (k', (U', V'))

       Invariant:
       If    . |- V : L
       and   . |- U : V
       and   K1 ||- V
       and   K2 ||- U
       and   K = K1, K2

       then  . |- V' : L
       and   V' = {{K}} V
       and   . |- U' : V'
       and   U' = [[K]] U
       and   . ||- V'
       and   . ||- U'
       and   k' = |K|
    *)
  (* abstractCtxs [G1,...,Gn] = G0, [G1',...,Gn']
       Invariants:
       If . |- G1,...,Gn ctx
          K ||- G1,...,Gn for some K
       then G0 |- G1',...,Gn' ctx for G0 = {{K}}
       and G1',...,Gn' nf
       and . ||- G1',...,Gn' ctx
    *)
  (* closedDec (G, D) = true iff D contains no EVar or FVar *)
  (* collectEVars (G, U[s], Xs) = Xs'
       Invariants:
         G |- U[s] : V
         Xs' extends Xs by new EVars in U[s]
    *)
  (* for the theorem prover:
       collect and abstract in subsitutions  including residual lemmas
       pending approval of Frank.
    *)
  (* abstractPVar (K, depth, L) = C'

       Invariant:
       If   G |- L : V
       and  |G| = depth
       and  L occurs in K  at kth position (starting at 1)
       then C' = Bidx (depth + k)
       and  {{K}}, G |- C' : V
    *)
  (* TC cannot contain free FVAR's or EVars'
            --cs  Fri Apr 30 13:45:50 2004 *)
  (* Argument must be in normal form *)
  (* enforced by reconstruction -kw
          val _ = checkType V'' *)
  (* enforced by reconstruction -kw
          val _ = checkType V'' *)
  (* What's happening with GX? *)
  (* What's happening with TCs? *)
  (* just added to abstract over residual lemmas  -cs *)
  (* Tomorrow: Make collection in program values a priority *)
  (* Then just traverse the Tomega by abstraction to get to the types of those
       variables. *)
  let raiseType = raiseType
  let raiseTerm = raiseTerm
  let piDepend = piDepend
  let closedDec = closedDec
  let closedSub = closedSub
  let closedExp = closedExp
  let abstractDecImp = abstractDecImp
  let abstractDef = abstractDef
  let abstractCtxs = abstractCtxs
  let abstractTomegaSub = abstractTomegaSub
  let abstractTomegaPrg = abstractTomegaPrg
  let abstractSpine = abstractSpineExt
  let collectEVars = collectEVars
  let collectEVarsSpine = collectEVarsSpine
  let closedCtx = closedCtx
  let closedCTX = closedCTX
end
(* functor Abstract *)

(* # 1 "src/lambda/Abstract.sml.ml" *)
