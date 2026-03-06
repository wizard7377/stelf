# 1 "src/m2/meta_abstract.sig.ml"
open! Basis;;
(* Meta Abstraction *);;
(* Author: Carsten Schuermann *);;
module type METAABSTRACT = sig
                           module MetaSyn : METASYN
                           exception Error of string 
                           val abstract : MetaSyn.state_ -> MetaSyn.state_
                           end;;
(* signature METAABSTRACT *);;
# 1 "src/m2/meta_abstract.fun.ml"
open! Basis;;
(* Meta Abstraction *);;
(* Author: Carsten Schuermann *);;
module MetaAbstract(MetaAbstract__0: sig
                                     module Global : GLOBAL
                                     module MetaSyn' : METASYN
                                     module MetaGlobal : METAGLOBAL
                                     module Abstract : ABSTRACT
                                     (*! sharing Abstract.IntSyn = MetaSyn'.IntSyn !*)
                                     module ModeTable : MODETABLE
                                     (*! sharing ModeSyn.IntSyn = MetaSyn'.IntSyn !*)
                                     module Whnf : WHNF
                                     (*! sharing Whnf.IntSyn = MetaSyn'.IntSyn !*)
                                     module Print : PRINT
                                     (*! sharing Print.IntSyn = MetaSyn'.IntSyn !*)
                                     module Constraints : CONSTRAINTS
                                     (*! sharing Constraints.IntSyn = MetaSyn'.IntSyn !*)
                                     module Unify : UNIFY
                                     (*! sharing Unify.IntSyn = MetaSyn'.IntSyn !*)
                                     module Names : NAMES
                                     (*! sharing Names.IntSyn = MetaSyn'.IntSyn !*)
                                     module TypeCheck : TYPECHECK
                                     (*! sharing TypeCheck.IntSyn = MetaSyn'.IntSyn !*)
                                     module Subordinate : SUBORDINATE
                                     end) : METAABSTRACT
  =
  struct
    module MetaSyn = MetaSyn';;
    exception Error of string ;;
    open!
      struct
        module I = IntSyn;;
        module S = Stream;;
        module M = MetaSyn;;
        module C = Constraints;;
        type var_ = | Ev of I.exp_ option ref * I.exp_ * MetaSyn.mode_ 
                    | Bv ;;
        let rec checkEmpty =
          function 
                   | [] -> ()
                   | cnstr_
                       -> begin
                          match C.simplify cnstr_
                          with 
                               | [] -> ()
                               | _
                                   -> raise
                                      ((Error "Unresolved constraints"))
                          end;;
        let rec typecheck (M.Prefix (g_, m_, b_), v_) =
          TypeCheck.typeCheck (g_, (v_, (I.Uni I.type_)));;
        let rec modeEq =
          function 
                   | (ModeSyn.Marg (plus_, _), top_) -> true
                   | (ModeSyn.Marg (minus_, _), bot_) -> true
                   | _ -> false;;
        let rec atxLookup =
          function 
                   | (null_, _) -> None
                   | (I.Decl (m_, Bv), r) -> atxLookup (m_, r)
                   | (I.Decl (m_, (Ev (r', _, _) as e_)), r) -> begin
                       if r = r' then (Some e_) else atxLookup (m_, r) end;;
        let rec raiseType =
          function 
                   | (0, g_, v_) -> v_
                   | (depth, I.Decl (g_, d_), v_)
                       -> raiseType
                          (depth - 1, g_, (I.Pi ((d_, I.maybe_), v_)));;
        let rec weaken =
          function 
                   | (0, g_, a) -> I.id
                   | (depth, I.Decl (g'_, (I.Dec (name, v_) as d_)), a)
                       -> let w' = weaken (depth - 1, g'_, a) in begin
                            if Subordinate.belowEq (I.targetFam v_, a) then
                            I.dot1 w' else I.comp (w', I.shift) end;;
        let rec countPi v_ =
          let rec countPi' =
            function 
                     | (I.Root _, n) -> n
                     | (I.Pi (_, v_), n) -> countPi' (v_, n + 1)
                     | (I.EClo (v_, _), n) -> countPi' (v_, n)
            in countPi' (v_, 0);;
        let rec collectExp (lG0, g_, us_, mode, adepth_) =
          collectExpW (lG0, g_, Whnf.whnf us_, mode, adepth_)
        and collectExpW =
          function 
                   | (lG0, g_, (I.Uni _, s), mode, adepth_) -> adepth_
                   | (lG0, g_, (I.Pi ((d_, _), v_), s), mode, adepth_)
                       -> collectExp
                          (lG0, (I.Decl (g_, I.decSub (d_, s))),
                           (v_, I.dot1 s), mode,
                           collectDec (lG0, g_, (d_, s), mode, adepth_))
                   | (lG0, g_, (I.Lam (d_, u_), s), mode, adepth_)
                       -> collectExp
                          (lG0, (I.Decl (g_, I.decSub (d_, s))),
                           (u_, I.dot1 s), mode,
                           collectDec (lG0, g_, (d_, s), mode, adepth_))
                   | (lG0, g_, ((I.Root (I.BVar k, s_), s) as us_), mode,
                      ((a_, depth) as adepth_))
                       -> let l = I.ctxLength g_ in begin
                            if (k = ((l + depth) - lG0)) && (depth > 0) then
                            let I.Dec (_, v_) = I.ctxDec (g_, k)
                              in collectSpine
                                 (lG0, g_, (s_, s), mode,
                                  ((I.Decl (a_, Bv)), depth - 1))
                            else
                            collectSpine (lG0, g_, (s_, s), mode, adepth_)
                            end
                   | (lG0, g_, (I.Root (c_, s_), s), mode, adepth_)
                       -> collectSpine (lG0, g_, (s_, s), mode, adepth_)
                   | (lG0, g_, (I.EVar (r, gx_, v_, cnstrs), s), mode,
                      ((a_, depth) as adepth_))
                       -> begin
                          match atxLookup (a_, r)
                          with 
                               | None
                                   -> let _ = checkEmpty (! cnstrs)
                                        in let lGp' =
                                             ((I.ctxLength gx_) - lG0) +
                                               depth
                                             in let w =
                                                  weaken
                                                  (lGp', gx_, I.targetFam v_)
                                                  in let iw = Whnf.invert w
                                                       in let gx'_ =
                                                            Whnf.strengthen
                                                            (iw, gx_)
                                                            in let lGp'' =
                                                                 ((I.ctxLength
                                                                   gx'_) -
                                                                    lG0)
                                                                   + depth
                                                                 in let
                                                                    vraised_
                                                                    =
                                                                    raiseType
                                                                    (lGp'',
                                                                    gx'_,
                                                                    (I.EClo
                                                                    (v_, iw)))
                                                                    in 
                                                                    let
                                                                    (I.EVar
                                                                    (r', _,
                                                                    _, _) as
                                                                    x'_) =
                                                                    I.newEVar
                                                                    (gx'_,
                                                                    (I.EClo
                                                                    (v_, iw)))
                                                                    in 
                                                                    let _ =
                                                                    Unify.instantiateEVar
                                                                    (r,
                                                                    (I.EClo
                                                                    (x'_, w)),
                                                                    [])
                                                                    in 
                                                                    collectSub
                                                                    (lG0, g_,
                                                                    lGp'', s,
                                                                    mode,
                                                                    ((I.Decl
                                                                    (a_,
                                                                    (Ev
                                                                    (r',
                                                                    vraised_,
                                                                    mode)))),
                                                                    depth))
                               | Some (Ev (_, v_, _))
                                   -> let lGp' = countPi v_
                                        in collectSub
                                           (lG0, g_, lGp', s, mode, adepth_)
                          end
                   | (lGO, g_, (I.FgnExp csfe, s), mode, adepth_)
                       -> I.FgnExpStd.fold
                          csfe
                          (function 
                                    | (u_, adepth'_)
                                        -> collectExp
                                           (lGO, g_, (u_, s), mode, adepth'_))
                          adepth_
        and collectSub =
          function 
                   | (_, _, 0, _, _, adepth_) -> adepth_
                   | (lG0, g_, lG', I.Shift k, mode, adepth_)
                       -> collectSub
                          (lG0, g_, lG',
                           (I.Dot ((I.Idx (k + 1)), (I.Shift (k + 1)))),
                           mode, adepth_)
                   | (lG0, g_, lG', I.Dot (I.Idx k, s), mode,
                      ((a_, depth) as adepth_))
                       -> collectSub (lG0, g_, lG' - 1, s, mode, adepth_)
                   | (lG0, g_, lG', I.Dot (I.Exp u_, s), mode, adepth_)
                       -> collectSub
                          (lG0, g_, lG' - 1, s, mode,
                           collectExp (lG0, g_, (u_, I.id), mode, adepth_))
        and collectSpine =
          function 
                   | (lG0, g_, (nil_, _), mode, adepth_) -> adepth_
                   | (lG0, g_, (I.SClo (s_, s'), s), mode, adepth_)
                       -> collectSpine
                          (lG0, g_, (s_, I.comp (s', s)), mode, adepth_)
                   | (lG0, g_, (I.App (u_, s_), s), mode, adepth_)
                       -> collectSpine
                          (lG0, g_, (s_, s), mode,
                           collectExp (lG0, g_, (u_, s), mode, adepth_))
        and collectDec (lG0, g_, (I.Dec (x, v_), s), mode, adepth_) =
          collectExp (lG0, g_, (v_, s), mode, adepth_);;
        let rec collectModeW =
          function 
                   | (lG0, g_, modeIn, modeRec,
                      (I.Root (I.Const cid, s_), s), adepth_)
                       -> let rec collectModeW' =
                            function 
                                     | (((nil_, _), mnil_), adepth_)
                                         -> adepth_
                                     | (((I.SClo (s_, s'), s), m_), adepth_)
                                         -> collectModeW'
                                            (((s_, I.comp (s', s)), m_),
                                             adepth_)
                                     | (((I.App (u_, s_), s), ModeSyn.Mapp
                                         (m, mS)),
                                        adepth_)
                                         -> collectModeW'
                                            (((s_, s), mS), begin
                                             if modeEq (m, modeIn) then
                                             collectExp
                                             (lG0, g_, (u_, s), modeRec,
                                              adepth_)
                                             else adepth_ end)
                            in let mS = valOf (ModeTable.modeLookup cid)
                                 in collectModeW' (((s_, s), mS), adepth_)
                   | (lG0, g_, modeIn, modeRec, (I.Pi ((d_, p_), v_), s),
                      adepth_)
                       -> raise
                          ((Error
                            "Implementation restricted to the Horn fragment of the meta logic"));;
        let rec collectG (lG0, g_, vs_, adepth_) =
          collectGW (lG0, g_, Whnf.whnf vs_, adepth_)
        and collectGW (lG0, g_, vs_, adepth_) =
          collectModeW
          (lG0, g_, M.bot_, M.top_, vs_,
           collectModeW (lG0, g_, M.top_, M.bot_, vs_, adepth_));;
        let rec collectDTop (lG0, g_, vs_, adepth_) =
          collectDTopW (lG0, g_, Whnf.whnf vs_, adepth_)
        and collectDTopW =
          function 
                   | (lG0, g_,
                      (I.Pi (((I.Dec (x, v1_) as d_), no_), v2_), s),
                      adepth_)
                       -> collectG
                          (lG0, g_, (v1_, s),
                           collectDTop
                           (lG0, (I.Decl (g_, I.decSub (d_, s))),
                            (v2_, I.dot1 s), adepth_))
                   | (lG0, g_, ((I.Root _, s) as vs_), adepth_)
                       -> collectModeW
                          (lG0, g_, M.top_, M.top_, vs_, adepth_);;
        let rec collectDBot (lG0, g_, vs_, adepth_) =
          collectDBotW (lG0, g_, Whnf.whnf vs_, adepth_)
        and collectDBotW =
          function 
                   | (lG0, g_, (I.Pi ((d_, _), v_), s), adepth_)
                       -> collectDBot
                          (lG0, (I.Decl (g_, I.decSub (d_, s))),
                           (v_, I.dot1 s), adepth_)
                   | (lG0, g_, ((I.Root _, s) as vs_), adepth_)
                       -> collectModeW
                          (lG0, g_, M.bot_, M.bot_, vs_, adepth_);;
        let rec collect (M.Prefix (g_, m_, b_), v_) =
          let lG0 = I.ctxLength g_
            in let (a_, k) =
                 collectDBot
                 (lG0, g_, (v_, I.id),
                  collectDTop (lG0, g_, (v_, I.id), (I.null_, lG0)))
                 in a_;;
        let rec lookupEV (a_, r) =
          let rec lookupEV' =
            function 
                     | (I.Decl (a_, Ev (r, v_, _)), r', k) -> begin
                         if r = r' then (k, v_) else
                         lookupEV' (a_, r', k + 1) end
                     | (I.Decl (a_, Bv), r', k) -> lookupEV' (a_, r', k + 1)
            in lookupEV' (a_, r, 1);;
        let rec lookupBV (a_, i) =
          let rec lookupBV' =
            function 
                     | (I.Decl (a_, Ev (r, v_, _)), i, k)
                         -> lookupBV' (a_, i, k + 1)
                     | (I.Decl (a_, Bv), 1, k) -> k
                     | (I.Decl (a_, Bv), i, k)
                         -> lookupBV' (a_, i - 1, k + 1)
            in lookupBV' (a_, i, 1);;
        let rec abstractExpW =
          function 
                   | (a_, g_, depth, ((I.Uni l_ as v_), s)) -> v_
                   | (a_, g_, depth, (I.Pi ((d_, p_), v_), s))
                       -> Abstract.piDepend
                          ((abstractDec (a_, g_, depth, (d_, s)), p_),
                           abstractExp
                           (a_, (I.Decl (g_, I.decSub (d_, s))), depth + 1,
                            (v_, I.dot1 s)))
                   | (a_, g_, depth, (I.Lam (d_, u_), s))
                       -> (I.Lam
                           (abstractDec (a_, g_, depth, (d_, s)),
                            abstractExp
                            (a_, (I.Decl (g_, I.decSub (d_, s))), depth + 1,
                             (u_, I.dot1 s))))
                   | (a_, g_, depth, (I.Root ((I.BVar k as c_), s_), s))
                       -> begin
                       if k > depth then
                       let k' = lookupBV (a_, k - depth)
                         in (I.Root
                             ((I.BVar (k' + depth)),
                              abstractSpine (a_, g_, depth, (s_, s))))
                       else
                       (I.Root (c_, abstractSpine (a_, g_, depth, (s_, s))))
                       end
                   | (a_, g_, depth, (I.Root (c_, s_), s))
                       -> (I.Root
                           (c_, abstractSpine (a_, g_, depth, (s_, s))))
                   | (a_, g_, depth, (I.EVar (r, _, v_, _), s))
                       -> let (k, vraised_) = lookupEV (a_, r)
                            in (I.Root
                                ((I.BVar (k + depth)),
                                 abstractSub
                                 (a_, g_, depth, (vraised_, I.id), s,
                                  I.targetFam v_, I.nil_)))
                   | (a_, g_, depth, (I.FgnExp csfe, s))
                       -> I.FgnExpStd.Map.apply
                          csfe
                          (function 
                                    | u_
                                        -> abstractExp
                                           (a_, g_, depth, (u_, s)))
        and abstractExp (a_, g_, depth, us_) =
          abstractExpW (a_, g_, depth, Whnf.whnf us_)
        and abstractSpine =
          function 
                   | (a_, g_, depth, (nil_, _)) -> I.nil_
                   | (a_, g_, depth, (I.App (u_, s_), s))
                       -> (I.App
                           (abstractExp (a_, g_, depth, (u_, s)),
                            abstractSpine (a_, g_, depth, (s_, s))))
                   | (a_, g_, depth, (I.SClo (s_, s'), s))
                       -> abstractSpine (a_, g_, depth, (s_, I.comp (s', s)))
        and abstractSub (a_, g_, depth, xVt_, s, b, s_) =
          abstractSubW (a_, g_, depth, Whnf.whnf xVt_, s, b, s_)
        and abstractSubW =
          function 
                   | (a_, g_, depth, (I.Root _, _), s, b, s_) -> s_
                   | (a_, g_, depth, ((I.Pi _, _) as xVt_), I.Shift k, b, s_)
                       -> abstractSub
                          (a_, g_, depth, xVt_,
                           (I.Dot ((I.Idx (k + 1)), (I.Shift (k + 1)))), b,
                           s_)
                   | (a_, g_, depth, ((I.Pi (_, xv'_), t) as xVt_), I.Dot
                      (I.Idx k, s), b, s_)
                       -> let I.Dec (x, v_) = I.ctxDec (g_, k) in begin
                            if k > depth then
                            let k' = lookupBV (a_, k - depth)
                              in abstractSub
                                 (a_, g_, depth, (xv'_, I.dot1 t), s, b,
                                  (I.App
                                   ((I.Root ((I.BVar (k' + depth)), I.nil_)),
                                    s_)))
                            else
                            abstractSub
                            (a_, g_, depth, (xv'_, I.dot1 t), s, b,
                             (I.App ((I.Root ((I.BVar k), I.nil_)), s_)))
                            end
                   | (a_, g_, depth, ((I.Pi (_, xv'_), t) as xVt_), I.Dot
                      (I.Exp u_, s), b, s_)
                       -> abstractSub
                          (a_, g_, depth, (xv'_, I.dot1 t), s, b,
                           (I.App
                            (abstractExp (a_, g_, depth, (u_, I.id)), s_)))
        and abstractDec (a_, g_, depth, (I.Dec (xOpt, v_), s)) =
          (I.Dec (xOpt, abstractExp (a_, g_, depth, (v_, s))));;
        let rec abstractCtx =
          function 
                   | (null_, (M.Prefix (null_, null_, null_) as gm_))
                       -> (gm_, I.null_)
                   | (I.Decl (a_, Bv), M.Prefix
                      (I.Decl (g_, d_), I.Decl (m_, marg), I.Decl (b_, b)))
                       -> let (M.Prefix (g'_, m'_, b'_), lG') =
                            abstractCtx (a_, (M.Prefix (g_, m_, b_)))
                            in let d'_ = abstractDec (a_, g_, 0, (d_, I.id))
                                 in let I.Dec (_, v_) = d'_
                                      in let _ = begin
                                           if ! Global.doubleCheck then
                                           typecheck
                                           ((M.Prefix (g'_, m'_, b'_)), v_)
                                           else () end
                                           in ((M.Prefix
                                                ((I.Decl
                                                  (g'_,
                                                   Names.decName (g'_, d'_))),
                                                 (I.Decl (m'_, marg)),
                                                 (I.Decl (b'_, b)))),
                                               (I.Decl (lG', d'_)))
                   | (I.Decl (a_, Ev (r, v_, m)), gm_)
                       -> let (M.Prefix (g'_, m'_, b'_), lG') =
                            abstractCtx (a_, gm_)
                            in let v''_ =
                                 abstractExp (a_, lG', 0, (v_, I.id))
                                 in let _ = begin
                                      if ! Global.doubleCheck then
                                      typecheck
                                      ((M.Prefix (g'_, m'_, b'_)), v''_) else
                                      () end
                                      in ((M.Prefix
                                           ((I.Decl
                                             (g'_,
                                              Names.decName
                                              (g'_, (I.Dec (None, v''_))))),
                                            (I.Decl (m'_, m)),
                                            (I.Decl
                                             (b'_,
                                              begin
                                              match m
                                              with 
                                                   | top_
                                                       -> !
                                                            MetaGlobal.maxSplit
                                                   | bot_ -> 0
                                              end)))),
                                          lG');;
        let rec abstract
          ((M.State (name, (M.Prefix (g_, m_, b_) as gm_), v_) as s_)) =
          let _ = Names.varReset I.null_
            in let a_ = collect (gm_, v_)
                 in let (gm'_, _) = abstractCtx (a_, gm_)
                      in let v'_ = abstractExp (a_, g_, 0, (v_, I.id))
                           in let s_ = (M.State (name, gm'_, v'_))
                                in let _ = begin
                                     if ! Global.doubleCheck then
                                     typecheck (gm'_, v'_) else () end in s_;;
        end;;
    (* Invariants? *);;
    (* Definition: Mode dependency order

       A pair ((G, M), V) is in mode dependency order iff
           G |- V : type
           G |- M modes
       and G = G0+, G1-, G1+,  ... G0-
       and V = {xn:Vn} ..{x1:V1}P0
       where G0+ collects all +variables when traversing P0 in order
       and Gi+ collects all +variables when traverseing Vi in order  (i > 0)
       and Gi- collects all -variables when traversing Vi in order   (i > 0)
       and G0- collects all -variables when traversing P0 in order.
    *);;
    (* Variable found during collect  *);;
    (* Var ::= EVar <r_, V, St>       *);;
    (*       | BV                     *);;
    (*--------------------------------------------------------------------*);;
    (* First section: Collecting EVars and BVars in mode dependency order *);;
    (*--------------------------------------------------------------------*);;
    (* checkEmpty Cnstr = ()
       raises Error exception if constraints Cnstr cannot be simplified
       to the empty constraint
    *);;
    (* Let G x A: defined as

       .      x .            = .
       (G, V) x (A, BVar)    = (G x A), V
       (G, V) x (A, EVar V') = (G, V x A), V'

       Then all A : Atx satisfy the following invariant: |- A Atx

       ? If    A = A', EV (r, V, m)
       ? then  . |- V = {G x A'}.V' : type
       ? where G x A' |- V' : type

       We write A ||- U if all EVars and BVars of U are collected in A,
       A ||- S if all EVars and BVars of S are collected in A,
       and similiar notation for the other syntactic categories.
    *);;
    (* typecheck ((G, M), V) = ()

       Invariant:
       If G |- V : type
       then typecheck returns ()
       else TypeCheck.Error is raised
    *);;
    (* modeEq (marg, st) = B'

       Invariant:
       If   (marg = + and st = top) or (marg = - and st = bot)
       then B' = true
       else B' = false
    *);;
    (* atxLookup (atx, r)  = Eopt'

       Invariant:
       If   r exists in atx as EV (V)
       then Eopt' = SOME EV and . |- V : type
       else Eopt' = NONE
    *);;
    (* raiseType (k, G, V) = {{G'}} V

       Invariant:
       If G |- V : L
          G = G0, G'  (so k <= |G|)
       then  G0 |- {{G'}} V : L
             |G'| = k

       All abstractions are potentially dependent.
    *);;
    (* weaken (depth,  G, a) = (w')
    *);;
    (* countPi V = n'

       If   G |- x : V
       and  V = {G'} V'
       then |G'| = n'
    *);;
    (* V in nf or enf? -fp *);;
    (* collectExp (lG0, G, (U, s), mode, (A, depth)) = (A', depth')
       collects EVar's and BVar's in mode dependency order!
       depth is needed to decide if a BVar is encountered for the first time.

       Invariant:
       Let A : auxiliary context,
           depth : length of the subcontext of G, which must still
                   be traversed and collected

       If   G  |- s : G'  and   G' |- U : V
       and  G = G0, G0', GO'', Gp
       and  . |- A Atx
       and  |G0,  G0', G0''| =  lG0
       and       |G0', G0''| = depth
       then           |G0''| = depth'
       and  . |- A' Atx
       and  A' = A, A''
       and  A'' ||- U [s]
    *);;
    (* impossible? *);;
    (* s = id *);;
    (* invariant: all variables (EV or BV) in V already seen! *);;
    (* lGp' >= 0 *);;
    (* lGp'' >= 0 *);;
    (* invariant: all variables (EV) in Vraised already seen *);;
    (* hack - should discuss with cs    -rv *);;
    (* collectSub (lG0, G, lG'', s, mode, (A, depth)) = (A', depth')
       collects EVar's and BVar's in mode dependency order!
       depth is needed to decide if a BVar is encountered for the first time.

       Invariant:
       Let A : auxiliary context,
           depth : length of the subcontext of G, which must still
                   be traversed and collected

       If   G  |- s : G'
       and  G = G0, G0', GO'', Gp
       and  . |- A Atx
       and  |G0,  G0', G0''| =  lG0
       and       |G0', G0''| = depth
       and  G' = GO, G''
       and  |G''| = lG''
       then           |G0''| = depth'
       and  . |- A' Atx
       and  A' = A, A''
       and  A'' ||- s   (for the first |G'| elements of s)
    *);;
    (* eta expansion *);;
    (* typing invariant guarantees that (EV, BV) in k : V already
             collected !! *);;
    (* typing invariant guarantees that (EV, BV) in V already
             collected !! *);;
    (* collectSpine (lG0, G, (S, s), mode, (A, depth)) = (A', depth')
       collects EVar's and BVar's in mode dependency order!
       depth is needed to decide if a BVar is encountered for the first time.

       Invariant:
       Let A : auxiliary context,
           depth : length of the subcontext of G, which must still
                   be traversed and collected

       If   G  |- s : G'  and   G' |- S : V > V'
       and  G = G0, G0', GO'', Gp
       and  . |- A Atx
       and  |G0,  G0', G0''| =  lG0
       and       |G0', G0''| = depth
       then           |G0''| = depth'
       and  . |- A' Atx
       and  A' = A, A''
       and  A'' ||- S
    *);;
    (* collectDec (lG0, G, (x:D, s), mode, (A, depth)) = (A', depth')
       collects EVar's and BVar's in mode dependency order!
       depth is needed to decide if a BVar is encountered for the first time.

       Invariant:
       Let A : auxiliary context,
           depth : length of the subcontext of G, which must still
                   be traversed and collected

       If   G  |- s : G'  and   G' |- D : L
       and  G = G0, G0', GO'', Gp
       and  . |- A Atx
       and  |G0,  G0', G0''| =  lG0
       and       |G0', G0''| = depth
       then           |G0''| = depth'
       and  . |- A' Atx
       and  A' = A, A''
       and  A'' ||- x:D[s]
    *);;
    (* collectModeW (lG0, G, modeIn, modeRec, (V, s) (A, depth)) = (A', depth')
       collects EVar's and BVar's in mode dependency order!
       depth is needed to decide if a BVar is encountered for the first time.

       Invariant:
       Let A : auxiliary context,
           depth : length of the subcontext of G, which must still
                   be traversed and collected

       If   G  |- s : G'  and   G' |- V : L        V[s] in whnf
       and  G = G0, G0', GO'', Gp
       and  . |- A Atx
       and  |G0,  G0', G0''| =  lG0
       and       |G0', G0''| = depth
       then           |G0''| = depth'
       and  . |- A' Atx
       and  A' = A, A''
       and  A'' ||- V
       and  A'' consists of all EVars/BVars marked with modeIn in V and
                recored as modeRec
    *);;
    (* s = id *);;
    (* collectG (lG0, G, (V, s) (A, depth)) = (A', depth')
       collects EVar's and BVar's in mode dependency order!
       depth is needed to decide if a BVar is encountered for the first time.

       Invariant:
       Let A : auxiliary context,
           depth : length of the subcontext of G, which must still
                   be traversed and collected

       If   G  |- s : G'  and   G' |- V : L
       and  G = G0, G0', GO'', Gp
       and  . |- A Atx
       and  |G0,  G0', G0''| =  lG0
       and       |G0', G0''| = depth
       then           |G0''| = depth'
       and  . |- A' Atx
       and  A' = A, A''
       and  A'' ||- V
       and  A'' consists of all Top EVars/BVars in the head of V
                    followed by Bot/Top EVars/BVars of recursive calls
                    (A'' is in mode dependecy order)
    *);;
    (* collectDTop (lG0, G, (V, s) (A, depth)) = (A', depth')
       collects EVar's and BVar's in mode dependency order!
       depth is needed to decide if a BVar is encountered for the first time.

       Invariant:
       Let A : auxiliary context,
           depth : length of the subcontext of G, which must still
                   be traversed and collected

       If   G  |- s : G'  and   G' |- V : L
       and  G = G0, G0', GO'', Gp
       and  . |- A Atx
       and  |G0,  G0', G0''| =  lG0
       and       |G0', G0''| = depth
       then           |G0''| = depth'
       and  . |- A' Atx
       and  A' = A, A''
       and  A'' ||- V
       and  A'' consists of all Top EVars/BVars in the head of V
                    followed by Bot/Top EVars/BVars of recursive calls
                    (A'' is in mode dependecy order)
    *);;
    (* only arrows *);;
    (* s = id *);;
    (* collectDBot (lG0, G, (V, s), (A, depth)) = (A', depth')
       collects EVar's and BVar's in mode dependency order!
       depth is needed to decide if a BVar is encountered for the first time.

       Invariant:
       Let A : auxiliary context,
           depth : length of the subcontext of G, which must still
                   be traversed and collected

       If   G  |- s : G'  and   G' |- V : L
       and  G = G0, G0', GO'', Gp
       and  . |- A Atx
       and  |G0,  G0', G0''| =  lG0
       and       |G0', G0''| = depth
       then           |G0''| = depth'
       and  . |- A' Atx
       and  A' = A, A''
       and  A'' ||- V
       and  A'' consists of all Top EVars/BVars in the head of V
                    followed by Bot/Top EVars/BVars of recursive calls
                    followed by Top EVars/BVars in the head of V
                    (A'' is in mode dependecy order)
    *);;
    (* s = id *);;
    (* collect ((G,_,_), V) = A'
       collects EVar's and BVar's in V mode dependency order.

       Invariant:
       If   G  |- s : G'  and   G' |- V : L
       then . |- A' Atx
       and  A' = A, A''
       and  A'' ||- V
       and  A'' consists of all Top EVars/BVars in the head of V
                    followed by Bot/Top EVars/BVars of recursive calls
                    followed by Top EVars/BVars in the head of V
                    (A'' is in mode dependecy order)
    *);;
    (*------------------------------------------------------------*);;
    (* Second section: Abstracting over EVars and BVars that have *);;
    (* been collected in mode dependency order                    *);;
    (*------------------------------------------------------------*);;
    (* lookupEV (A, r) = (k', V')

       Invariant:

       If   A ||- V
       and  G |- X : V' occuring in V
       then G x A |- k : V'
       and  . |- V' : type
    *);;
    (* lookupEV' I.Null cannot occur by invariant *);;
    (* lookupBV (A, i) = k'

       Invariant:

       If   A ||- V
       and  G |- V type
       and  G [x] A |- i : V'
       then ex a substititution  G x A |- s : G [x] A
       and  G x A |- k' : V''
       and  G x A |- V' [s] = V'' : type
    *);;
    (* lookupBV' I.Null cannot occur by invariant *);;
    (* abstractExpW (A, G, depth, (U, s)) = U'

       Invariant:
       If    G0, G |- s : G1   G1 |- U : V    (U,s) in whnf
       and   |G| = depth
       and   A is auxiliary context in mode dependency order
       and   A ||- U  and  A ||- V
       then  G0 x A, G |- U' : V'
       and   . ||- U' and . ||- V'
       and   U' is in nf
    *);;
    (* s = id *);;
    (* s = id *);;
    (* IMPROVE: remove the raised variable, replace by V -cs ?-fp *);;
    (* hack - should discuss with cs     -rv *);;
    (* abstractExp, same as abstractExpW, but (V, s) need not be in whnf *);;
    (* abstractSpine (A, G, depth, (S, s)) = U'

       Invariant:
       If    G0, G |- s : G1   G1 |- S : V1 > V2
       and   |G| = depth
       and   A is auxiliary context in mode dependency order
       and   A ||- U  and  H ||- V1
       then  G0 x A, G |- S' : V1' > V2'
       and   . ||- S' and . ||- V1'
    *);;
    (* abstractSub (A, G, depth, (XV, t), s, b, S) = S'

       Invariant:
       If    G0, G |- s : G'
       and   |G| = depth
       and   A is auxiliary context in mode dependency order
       and   A ||- s
       then  G0 x A, G |- S' : {XV [t]}.W > W
       and   . ||- S'
    *);;
    (* optimize: whnf not necessary *);;
    (* abstractDec (A, G, depth, (x:V, s)) = x:V'

       Invariant:
       If    G0, G |- s : G1   G1 |- V : L
       and   |G| = G
       and   |G| = depth
       and   A is auxiliary context in mode dependency order
       and   A ||- V
       then  G0 x A, G |- V' : L
       and   . ||- V'
    *);;
    (* abstractCtx (A, (G, M)) = ((G', M') , G'')

       Let E be a list of EVars possibly occuring in G

       Invariant:
       G' = G x A
       M' = M x A    (similar to G x A, but just represents mode information)
       G'' = G [x] A
    *);;
    (* abstract ((G, M), V) = ((G', M') , V')

       Invariant:
       If    G |- V : type    (M modes associated with G)
       then  G' |- V' : type  (M' modes associated with G')
       and   . ||- V'
    *);;
    let abstract = abstract;;
    end;;
(*! sharing Subordinate.IntSyn = MetaSyn'.IntSyn  !*);;
(* local *);;
(* functor MetaAbstract *);;
# 1 "src/m2/meta_abstract.sml.ml"
