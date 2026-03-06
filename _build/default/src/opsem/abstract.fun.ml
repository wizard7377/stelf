open! Basis;;
(* Abstraction *);;
(* Author: Frank Pfenning, Carsten Schuermann *);;
(* Modified: Roberto Virga, Brigitte Pientka *);;
module AbstractTabled(AbstractTabled__0: sig
                                         (*! structure IntSyn' : INTSYN !*)
                                         module Whnf : WHNF
                                         (*! sharing Whnf.IntSyn = IntSyn' !*)
                                         module Unify : UNIFY
                                         (*! sharing Unify.IntSyn = IntSyn' !*)
                                         module Constraints : CONSTRAINTS
                                         (*! sharing Constraints.IntSyn = IntSyn' !*)
                                         module Subordinate : SUBORDINATE
                                         (*! sharing Subordinate.IntSyn = IntSyn' !*)
                                         module Print : PRINT
                                         (*! sharing Print.IntSyn = IntSyn' !*)
                                         module Conv : CONV
                                         end) : ABSTRACTTABLED
  =
  struct
    (*! structure IntSyn = IntSyn' !*);;
    (*! structure TableParam = TableParam !*);;
    exception Error of string ;;
    open!
      struct
        module I = IntSyn;;
        module C = CompSyn;;
        type duplicates_ = | Av of I.exp_ * int 
                           | Fgn of int ;;
        type seenIn = | TypeLabel 
                      | Body ;;
        type existVars_ = | Ev of I.exp_ ;;
        let rec lengthSub =
          function 
                   | I.Shift n -> 0
                   | I.Dot (e_, s) -> 1 + (lengthSub s);;
        let rec compose' =
          function 
                   | (null_, g_) -> g_
                   | (IntSyn.Decl (g'_, d_), g_)
                       -> (IntSyn.Decl (compose' (g'_, g_), d_));;
        let rec isId =
          function 
                   | I.Shift n -> n = 0
                   | (I.Dot (I.Idx n, s') as s) -> isId' (s, 0)
                   | (I.Dot (undef_, s') as s) -> isId' (s, 0)
                   | I.Dot (I.Exp _, s) -> false
        and isId' =
          function 
                   | (I.Shift n, k) -> n = k
                   | (I.Dot (I.Idx i, s), k)
                       -> let k' = k + 1 in (i = k') && (isId' (s, k'))
                   | (I.Dot (undef_, s), k) -> isId' (s, k + 1);;
        let rec equalCtx =
          function 
                   | (null_, s, null_, s') -> true
                   | (I.Decl (g_, d_), s, I.Decl (g'_, d'_), s')
                       -> (Conv.convDec ((d_, s), (d'_, s'))) &&
                            (equalCtx (g_, I.dot1 s, g'_, I.dot1 s'))
                   | (I.Decl (g_, d_), s, null_, s') -> false
                   | (null_, s, I.Decl (g'_, d'_), s') -> false;;
        let rec eqEVarW arg__1 arg__2 =
          begin
          match (arg__1, arg__2)
          with 
               | (I.EVar (r1, _, _, _), Ev (I.EVar (r2, _, _, _))) -> r1 = r2
               | (_, _) -> false
          end;;
        let rec eqEVar x1_ (Ev x2_) =
          let (x1'_, s) = Whnf.whnf (x1_, I.id)
            in let (x2'_, s) = Whnf.whnf (x2_, I.id)
                 in eqEVarW x1'_ ((Ev x2'_));;
        let rec member' p_ k_ =
          let rec exists' =
            function 
                     | null_ -> None
                     | I.Decl (k'_, (l, Ev y_)) -> begin
                         if p_ ((Ev y_)) then (Some l) else exists' k'_ end
            in exists' k_;;
        let rec member p_ k_ =
          let rec exists' =
            function 
                     | null_ -> None
                     | I.Decl (k'_, (i, y_)) -> begin
                         if p_ y_ then (Some i) else exists' k'_ end
            in exists' k_;;
        let rec update' p_ k_ =
          let rec update' =
            function 
                     | null_ -> I.null_
                     | I.Decl (k'_, (label, y_)) -> begin
                         if p_ y_ then (I.Decl (k'_, (Body, y_))) else
                         (I.Decl (update' k'_, (label, y_))) end
            in update' k_;;
        let rec update p_ k_ =
          let rec update' =
            function 
                     | null_ -> I.null_
                     | I.Decl (k'_, ((label, i), y_)) -> begin
                         if p_ y_ then (I.Decl (k'_, ((Body, i), y_))) else
                         (I.Decl (update' k'_, ((label, i), y_))) end
            in update' k_;;
        let rec ( or ) =
          function 
                   | (maybe_, _) -> I.maybe_
                   | (_, maybe_) -> I.maybe_
                   | (meta_, _) -> I.meta_
                   | (_, meta_) -> I.meta_
                   | (no_, no_) -> I.no_;;
        let rec occursInExp =
          function 
                   | (k, I.Uni _) -> I.no_
                   | (k, I.Pi (dp_, v_))
                       -> ( or )
                            (occursInDecP (k, dp_), occursInExp (k + 1, v_))
                   | (k, I.Root (h_, s_))
                       -> occursInHead (k, h_, occursInSpine (k, s_))
                   | (k, I.Lam (d_, v_))
                       -> ( or )
                            (occursInDec (k, d_), occursInExp (k + 1, v_))
                   | (k, I.FgnExp csfe)
                       -> I.FgnExpStd.fold
                          csfe
                          (function 
                                    | (u_, dp_)
                                        -> ( or )
                                             (dp_,
                                              occursInExp
                                              (k, Whnf.normalize (u_, I.id))))
                          I.no_
        and occursInHead =
          function 
                   | (k, I.BVar k', dp_) -> begin
                       if k = k' then I.maybe_ else dp_ end
                   | (k, I.Const _, dp_) -> dp_
                   | (k, I.Def _, dp_) -> dp_
                   | (k, I.FgnConst _, dp_) -> dp_
                   | (k, I.Skonst _, no_) -> I.no_
                   | (k, I.Skonst _, meta_) -> I.meta_
                   | (k, I.Skonst _, maybe_) -> I.meta_
        and occursInSpine =
          function 
                   | (_, nil_) -> I.no_
                   | (k, I.App (u_, s_))
                       -> ( or ) (occursInExp (k, u_), occursInSpine (k, s_))
        and occursInDec (k, I.Dec (_, v_)) = occursInExp (k, v_)
        and occursInDecP (k, (d_, _)) = occursInDec (k, d_);;
        let rec piDepend =
          function 
                   | (((d_, no_), v_) as dpv_) -> (I.Pi dpv_)
                   | (((d_, meta_), v_) as dpv_) -> (I.Pi dpv_)
                   | ((d_, maybe_), v_)
                       -> (I.Pi ((d_, occursInExp (1, v_)), v_));;
        let rec raiseType =
          function 
                   | (null_, v_) -> v_
                   | (I.Decl (g_, d_), v_)
                       -> raiseType (g_, (I.Pi ((d_, I.maybe_), v_)));;
        let rec reverseCtx =
          function 
                   | (null_, g_) -> g_
                   | (I.Decl (g_, d_), g'_)
                       -> reverseCtx (g_, (I.Decl (g'_, d_)));;
        let rec ctxToEVarSub =
          function 
                   | (null_, s) -> s
                   | (IntSyn.Decl (g_, IntSyn.Dec (_, a_)), s)
                       -> let s' = ctxToEVarSub (g_, s)
                            in let x_ =
                                 IntSyn.newEVar
                                 (IntSyn.null_, (I.EClo (a_, s')))
                                 in (IntSyn.Dot ((IntSyn.Exp x_), s'));;
        let rec collectExpW =
          function 
                   | (gss_, gl_, (I.Uni l_, s), k_, dupVars_, flag, d)
                       -> (k_, dupVars_)
                   | (gss_, gl_, (I.Pi ((d_, _), v_), s), k_, dupVars_, flag,
                      d)
                       -> let (k'_, _) =
                            collectDec
                            (gss_, (d_, s), (k_, dupVars_), d, false)
                            in collectExp
                               (gss_, (I.Decl (gl_, I.decSub (d_, s))),
                                (v_, I.dot1 s), k'_, dupVars_, flag, d)
                   | (gss_, gl_, (I.Root (_, s_), s), k_, dupVars_, flag, d)
                       -> collectSpine
                          (gss_, gl_, (s_, s), k_, dupVars_, flag, d)
                   | (gss_, gl_, (I.Lam (d_, u_), s), k_, dupVars_, flag, d)
                       -> let (k'_, _) =
                            collectDec
                            (gss_, (d_, s), (k_, dupVars_), d, false)
                            in collectExp
                               (gss_, (I.Decl (gl_, I.decSub (d_, s))),
                                (u_, I.dot1 s), k'_, dupVars_, flag, 
                                d + 1)
                   | (gss_, gl_, ((I.EVar (r, gx_, v_, cnstrs) as x_), s),
                      k_, dupVars_, flag, d)
                       -> collectEVar
                          (gss_, gl_, (x_, s), k_, dupVars_, flag, d)
                   | (gss_, gl_, (I.FgnExp csfe, s), k_, dupVars_, flag, d)
                       -> I.FgnExpStd.fold
                          csfe
                          (function 
                                    | (u_, kd'_)
                                        -> let (k'_, dup_) = kd'_
                                             in collectExp
                                                (gss_, gl_, (u_, s), k'_,
                                                 dup_, false, d))
                          (k_, (I.Decl (dupVars_, (Fgn d))))
        and collectExp (gss_, gl_, us_, k_, dupVars_, flag, d) =
          collectExpW (gss_, gl_, Whnf.whnf us_, k_, dupVars_, flag, d)
        and collectSpine =
          function 
                   | (gss_, gl_, (nil_, _), k_, dupVars_, flag, d)
                       -> (k_, dupVars_)
                   | (gss_, gl_, (I.SClo (s_, s'), s), k_, dupVars_, flag, d)
                       -> collectSpine
                          (gss_, gl_, (s_, I.comp (s', s)), k_, dupVars_,
                           flag, d)
                   | (gss_, gl_, (I.App (u_, s_), s), k_, dupVars_, flag, d)
                       -> let (k'_, dupVars'_) =
                            collectExp
                            (gss_, gl_, (u_, s), k_, dupVars_, flag, d)
                            in collectSpine
                               (gss_, gl_, (s_, s), k'_, dupVars'_, flag, d)
        and collectEVarFapStr
          (gss_, gl_, ((x'_, v'_), w),
           ((I.EVar (r, gx_, v_, cnstrs) as x_), s), k_, dupVars_, flag, d)
          =
          begin
          match member' (eqEVar x_) k_
          with 
               | Some label -> begin
                   if flag then
                   collectSub
                   (gss_, gl_, s, k_, (I.Decl (dupVars_, (Av (x_, d)))),
                    flag, d)
                   else collectSub (gss_, gl_, s, k_, dupVars_, flag, d) end
               | None
                   -> let label = begin if flag then Body else TypeLabel end
                        in let (k'_, dupVars'_) =
                             collectExp
                             ((I.null_, I.id), I.null_, (v'_, I.id), k_,
                              dupVars_, false, d)
                             in collectSub
                                (gss_, gl_, I.comp (w, s),
                                 (I.Decl (k'_, (label, (Ev x'_)))),
                                 dupVars'_, flag, d)
          end
        and collectEVarNFapStr
          (gss_, gl_, ((x'_, v'_), w),
           ((I.EVar (r, gx_, v_, cnstrs) as x_), s), k_, dupVars_, flag, d)
          =
          begin
          match member' (eqEVar x_) k_
          with 
               | Some label -> begin
                   if flag then
                   collectSub
                   (gss_, gl_, s, k_, (I.Decl (dupVars_, (Av (x_, d)))),
                    flag, d)
                   else collectSub (gss_, gl_, s, k_, dupVars_, flag, d) end
               | None
                   -> let label = begin if flag then Body else TypeLabel end
                        in let (k'_, dupVars'_) =
                             collectExp
                             ((I.null_, I.id), I.null_, (v'_, I.id), k_,
                              dupVars_, false, d)
                             in begin
                             if flag then
                             collectSub
                             (gss_, gl_, I.comp (w, s),
                              (I.Decl (k'_, (label, (Ev x'_)))),
                              (I.Decl (dupVars'_, (Av (x'_, d)))), flag, d)
                             else
                             collectSub
                             (gss_, gl_, I.comp (w, s),
                              (I.Decl (k'_, (label, (Ev x'_)))), dupVars'_,
                              flag, d)
                             end
          end
        and collectEVarStr
          (((gs_, ss) as gss_), gl_,
           ((I.EVar (r, gx_, v_, cnstrs) as x_), s), k_, dupVars_, flag, d)
          =
          let w = Subordinate.weaken (gx_, I.targetFam v_)
            in let iw = Whnf.invert w
                 in let gx'_ = Whnf.strengthen (iw, gx_)
                      in let (I.EVar (r', _, _, _) as x'_) =
                           I.newEVar (gx'_, (I.EClo (v_, iw)))
                           in let _ =
                                Unify.instantiateEVar
                                (r, (I.EClo (x'_, w)), [])
                                in let v'_ =
                                     raiseType (gx'_, (I.EClo (v_, iw)))
                                     in begin
                                     if isId (I.comp (w, I.comp (ss, s)))
                                     then
                                     collectEVarFapStr
                                     (gss_, gl_, ((x'_, v'_), w), (x_, s),
                                      k_, dupVars_, flag, d)
                                     else
                                     collectEVarNFapStr
                                     (gss_, gl_, ((x'_, v'_), w), (x_, s),
                                      k_, dupVars_, flag, d)
                                     end
        and collectEVarFap
          (gss_, gl_, ((I.EVar (r, gx_, v_, cnstrs) as x_), s), k_, dupVars_,
           flag, d)
          =
          begin
          match member (eqEVar x_) k_
          with 
               | Some label -> begin
                   if flag then
                   collectSub
                   (gss_, gl_, s, k_, (I.Decl (dupVars_, (Av (x_, d)))),
                    flag, d)
                   else collectSub (gss_, gl_, s, k_, dupVars_, flag, d) end
               | None
                   -> let label = begin if flag then Body else TypeLabel end
                        in let v'_ = raiseType (gx_, v_)
                             in let (k'_, dupVars'_) =
                                  collectExp
                                  ((I.null_, I.id), I.null_, (v'_, I.id), k_,
                                   dupVars_, false, d)
                                  in collectSub
                                     (gss_, gl_, s,
                                      (I.Decl (k'_, (label, (Ev x_)))),
                                      dupVars'_, flag, d)
          end
        and collectEVarNFap
          (gss_, gl_, ((I.EVar (r, gx_, v_, cnstrs) as x_), s), k_, dupVars_,
           flag, d)
          =
          begin
          match member' (eqEVar x_) k_
          with 
               | Some label -> begin
                   if flag then
                   collectSub
                   (gss_, gl_, s, k_, (I.Decl (dupVars_, (Av (x_, d)))),
                    flag, d)
                   else collectSub (gss_, gl_, s, k_, dupVars_, flag, d) end
               | None
                   -> let label = begin if flag then Body else TypeLabel end
                        in let v'_ = raiseType (gx_, v_)
                             in let (k'_, dupVars'_) =
                                  collectExp
                                  ((I.null_, I.id), I.null_, (v'_, I.id), k_,
                                   dupVars_, false, d)
                                  in begin
                                  if flag then
                                  collectSub
                                  (gss_, gl_, s,
                                   (I.Decl (k'_, (label, (Ev x_)))),
                                   (I.Decl (dupVars_, (Av (x_, d)))), flag,
                                   d)
                                  else
                                  collectSub
                                  (gss_, gl_, s,
                                   (I.Decl (k'_, (label, (Ev x_)))),
                                   dupVars_, flag, d)
                                  end
          end
        and collectEVar
          (gss_, gl_, ((I.EVar (r, gx_, v_, cnstrs) as x_), s), k_, dupVars_,
           flag, d)
          = begin
          if ! TableParam.strengthen then
          collectEVarStr (gss_, gl_, (x_, s), k_, dupVars_, flag, d) else
          begin
          if isId s then
          collectEVarFap (gss_, gl_, (x_, s), k_, dupVars_, flag, d) else
          collectEVarNFap (gss_, gl_, (x_, s), k_, dupVars_, flag, d) end end
        and collectDec (gss_, (I.Dec (_, v_), s), (k_, dupVars_), d, flag) =
          let (k'_, dupVars'_) =
            collectExp (gss_, I.null_, (v_, s), k_, dupVars_, flag, d)
            in (k'_, dupVars'_)
        and collectSub =
          function 
                   | (gss_, gl_, I.Shift _, k_, dupVars_, flag, d)
                       -> (k_, dupVars_)
                   | (gss_, gl_, I.Dot (I.Idx _, s), k_, dupVars_, flag, d)
                       -> collectSub (gss_, gl_, s, k_, dupVars_, flag, d)
                   | (gss_, gl_, I.Dot
                      (I.Exp
                       ((I.EVar ({ contents = Some u_}, _, _, _) as x_)), s),
                      k_, dupVars_, flag, d)
                       -> let u'_ = Whnf.normalize (u_, I.id)
                            in let (k'_, dupVars'_) =
                                 collectExp
                                 (gss_, gl_, (u'_, I.id), k_, dupVars_, flag,
                                  d)
                                 in collectSub
                                    (gss_, gl_, s, k'_, dupVars'_, flag, d)
                   | (gss_, gl_, I.Dot
                      (I.Exp ((I.AVar { contents = Some u'_} as u_)), s), k_,
                      dupVars_, flag, d)
                       -> let (k'_, dupVars'_) =
                            collectExp
                            (gss_, gl_, (u'_, I.id), k_, dupVars_, flag, d)
                            in collectSub
                               (gss_, gl_, s, k'_, dupVars'_, flag, d)
                   | (gss_, gl_, I.Dot (I.Exp (I.EClo (u'_, s')), s), k_,
                      dupVars_, flag, d)
                       -> let u_ = Whnf.normalize (u'_, s')
                            in let (k'_, dupVars'_) =
                                 collectExp
                                 (gss_, gl_, (u_, I.id), k_, dupVars_, flag,
                                  d)
                                 in collectSub
                                    (gss_, gl_, s, k'_, dupVars'_, flag, d)
                   | (gss_, gl_, I.Dot (I.Exp u_, s), k_, dupVars_, flag, d)
                       -> let (k'_, dupVars'_) =
                            collectExp
                            (gss_, gl_, (u_, I.id), k_, dupVars_, flag, d)
                            in collectSub
                               (gss_, gl_, s, k'_, dupVars'_, flag, d)
                   | (gss_, gl_, I.Dot (undef_, s), k_, dupVars_, flag, d)
                       -> collectSub (gss_, gl_, s, k_, dupVars_, flag, d);;
        let rec collectCtx =
          function 
                   | (gss_, C.DProg (null_, null_), (k_, dupVars_), d)
                       -> (k_, dupVars_)
                   | (gss_, C.DProg
                      (I.Decl (g_, d_), I.Decl (dPool, parameter_)),
                      (k_, dupVars_), d)
                       -> let (k'_, dupVars'_) =
                            collectCtx
                            (gss_, (C.DProg (g_, dPool)), (k_, dupVars_),
                             d - 1)
                            in collectDec
                               (gss_, (d_, I.id), (k'_, dupVars'_), d - 1,
                                false)
                   | (gss_, C.DProg
                      (I.Decl (g_, d_), I.Decl (dPool, C.Dec (r, s, ha_))),
                      (k_, dupVars_), d)
                       -> let (k'_, dupVars'_) =
                            collectCtx
                            (gss_, (C.DProg (g_, dPool)), (k_, dupVars_),
                             d - 1)
                            in collectDec
                               (gss_, (d_, I.id), (k'_, dupVars'_), d - 1,
                                false);;
        let rec abstractExpW =
          function 
                   | (flag, gs_, posEA, vars_, gl_, total, depth,
                      ((I.Uni l_ as u_), s), eqn) -> (posEA, vars_, u_, eqn)
                   | (flag, gs_, posEA, vars_, gl_, total, depth,
                      (I.Pi ((d_, p_), v_), s), eqn)
                       -> let (posEA', vars'_, d_, _) =
                            abstractDec
                            (gs_, posEA, vars_, gl_, total, depth, (d_, s),
                             None)
                            in let (posEA'', vars''_, v'_, eqn2) =
                                 abstractExp
                                 (flag, gs_, posEA', vars'_, gl_, total,
                                  depth + 1, (v_, I.dot1 s), eqn)
                                 in (posEA'', vars''_,
                                     piDepend ((d_, p_), v'_), eqn2)
                   | (flag, gs_, posEA, vars_, gl_, total, depth,
                      (I.Root (h_, s_), s), eqn)
                       -> let (posEA', vars'_, s_, eqn') =
                            abstractSpine
                            (flag, gs_, posEA, vars_, gl_, total, depth,
                             (s_, s), eqn)
                            in (posEA', vars'_, (I.Root (h_, s_)), eqn')
                   | (flag, gs_, posEA, vars_, gl_, total, depth,
                      (I.Lam (d_, u_), s), eqn)
                       -> let (posEA', vars'_, d'_, _) =
                            abstractDec
                            (gs_, posEA, vars_, gl_, total, depth, (d_, s),
                             None)
                            in let (posEA'', vars''_, u'_, eqn2) =
                                 abstractExp
                                 (flag, gs_, posEA', vars'_,
                                  (I.Decl (gl_, d'_)), total, depth + 1,
                                  (u_, I.dot1 s), eqn)
                                 in (posEA'', vars''_, (I.Lam (d'_, u'_)),
                                     eqn2)
                   | (flag, ((gss_, ss) as gs_), ((epos, apos) as posEA),
                      vars_, gl_, total, depth,
                      ((I.EVar (_, gx_, vx_, _) as x_), s), eqn) -> begin
                       if isId (I.comp (ss, s)) then
                       abstractEVarFap
                       (flag, gs_, posEA, vars_, gl_, total, depth, (x_, s),
                        eqn)
                       else
                       abstractEVarNFap
                       (flag, gs_, posEA, vars_, gl_, total, depth, (x_, s),
                        eqn)
                       end
        and abstractExp
          (flag, gs_, posEA, vars_, gl_, total, depth, us_, eqn) =
          abstractExpW
          (flag, gs_, posEA, vars_, gl_, total, depth, Whnf.whnf us_, eqn)
        and abstractEVarFap
          (flag, gs_, ((epos, apos) as posEA), vars_, gl_, total, depth,
           (x_, s), eqn)
          =
          begin
          match member (eqEVar x_) vars_
          with 
               | Some (label, i) -> begin
                   if flag then
                   begin
                   match label
                   with 
                        | Body
                            -> let Bv = (I.BVar (apos + depth))
                                 in let bv'_ = (I.BVar (i + depth))
                                      in let bv1_ = (I.BVar (apos + depth))
                                           in let (posEA', vars'_, s_, eqn1)
                                                =
                                                abstractSub
                                                (flag, gs_, (epos, apos - 1),
                                                 vars_, gl_, total, depth, s,
                                                 I.nil_, eqn)
                                                in (posEA', vars'_,
                                                    (I.Root (Bv, I.nil_)),
                                                    (TableParam.Unify
                                                     (gl_,
                                                      (I.Root (bv'_, s_)),
                                                      (I.Root (bv1_, I.nil_)),
                                                      eqn1)))
                        | TypeLabel
                            -> let vars'_ = update (eqEVar x_) vars_
                                 in let (posEA', vars''_, s_, eqn1) =
                                      abstractSub
                                      (flag, gs_, (epos, apos), vars'_, gl_,
                                       total, depth, s, I.nil_, eqn)
                                      in (posEA', vars''_,
                                          (I.Root ((I.BVar (i + depth)), s_)),
                                          eqn1)
                   end else
                   let (posEA', vars'_, s_, eqn1) =
                     abstractSub
                     (flag, gs_, (epos, apos), vars_, gl_, total, depth, s,
                      I.nil_, eqn)
                     in (posEA', vars'_, (I.Root ((I.BVar (i + depth)), s_)),
                         eqn1)
                   end
               | None
                   -> let label = begin if flag then Body else TypeLabel end
                        in let Bv = (I.BVar (epos + depth))
                             in let pos = (epos - 1, apos)
                                  in let (posEA', vars'_, s_, eqn1) =
                                       abstractSub
                                       (flag, gs_, pos,
                                        (I.Decl
                                         (vars_, ((label, epos), (Ev x_)))),
                                        gl_, total, depth, s, I.nil_, eqn)
                                       in (posEA', vars'_, (I.Root (Bv, s_)),
                                           eqn1)
          end
        and abstractEVarNFap
          (flag, gs_, ((epos, apos) as posEA), vars_, gl_, total, depth,
           (x_, s), eqn)
          =
          begin
          match member (eqEVar x_) vars_
          with 
               | Some (label, i) -> begin
                   if flag then
                   let Bv = (I.BVar (apos + depth))
                     in let bv'_ = (I.BVar (i + depth))
                          in let bv1_ = (I.BVar (apos + depth))
                               in let (posEA', vars'_, s_, eqn1) =
                                    abstractSub
                                    (flag, gs_, (epos, apos - 1), vars_, gl_,
                                     total, depth, s, I.nil_, eqn)
                                    in (posEA', vars'_,
                                        (I.Root (Bv, I.nil_)),
                                        (TableParam.Unify
                                         (gl_, (I.Root (bv'_, s_)),
                                          (I.Root (bv1_, I.nil_)), eqn1)))
                   else
                   let (posEA', vars'_, s_, eqn1) =
                     abstractSub
                     (flag, gs_, (epos, apos), vars_, gl_, total, depth, s,
                      I.nil_, eqn)
                     in (posEA', vars'_, (I.Root ((I.BVar (i + depth)), s_)),
                         eqn1)
                   end
               | None -> begin
                   if flag then
                   let label = begin if flag then Body else TypeLabel end
                     in let Bv = (I.BVar (apos + depth))
                          in let bv'_ = (I.BVar (epos + depth))
                               in let bv1_ = (I.BVar (apos + depth))
                                    in let (posEA', vars'_, s_, eqn1) =
                                         abstractSub
                                         (flag, gs_, (epos - 1, apos - 1),
                                          (I.Decl
                                           (vars_, ((label, epos), (Ev x_)))),
                                          gl_, total, depth, s, I.nil_, eqn)
                                         in (posEA', vars'_,
                                             (I.Root (Bv, I.nil_)),
                                             (TableParam.Unify
                                              (gl_, (I.Root (bv'_, s_)),
                                               (I.Root (bv1_, I.nil_)), eqn1)))
                   else
                   let (posEA', vars'_, s_, eqn1) =
                     abstractSub
                     (flag, gs_, (epos - 1, apos),
                      (I.Decl (vars_, ((TypeLabel, epos), (Ev x_)))), gl_,
                      total, depth, s, I.nil_, eqn)
                     in (posEA', vars'_,
                         (I.Root ((I.BVar (epos + depth)), s_)), eqn1)
                   end
          end
        and abstractSub =
          function 
                   | (flag, gs_, posEA, vars_, gl_, total, depth, I.Shift k,
                      s_, eqn) -> begin
                       if k < depth then
                       abstractSub
                       (flag, gs_, posEA, vars_, gl_, total, depth,
                        (I.Dot ((I.Idx (k + 1)), (I.Shift (k + 1)))), s_,
                        eqn)
                       else (posEA, vars_, s_, eqn) end
                   | (flag, gs_, posEA, vars_, gl_, total, depth, I.Dot
                      (I.Idx k, s), s_, eqn)
                       -> abstractSub
                          (flag, gs_, posEA, vars_, gl_, total, depth, s,
                           (I.App ((I.Root ((I.BVar k), I.nil_)), s_)), eqn)
                   | (flag, gs_, posEA, vars_, gl_, total, depth, I.Dot
                      (I.Exp u_, s), s_, eqn)
                       -> let (posEA', vars'_, u'_, eqn') =
                            abstractExp
                            (flag, gs_, posEA, vars_, gl_, total, depth,
                             (u_, I.id), eqn)
                            in abstractSub
                               (flag, gs_, posEA', vars'_, gl_, total, depth,
                                s, (I.App (u'_, s_)), eqn')
        and abstractSpine =
          function 
                   | (flag, gs_, posEA, vars_, gl_, total, depth, (nil_, _),
                      eqn) -> (posEA, vars_, I.nil_, eqn)
                   | (flag, gs_, posEA, vars_, gl_, total, depth,
                      (I.SClo (s_, s'), s), eqn)
                       -> abstractSpine
                          (flag, gs_, posEA, vars_, gl_, total, depth,
                           (s_, I.comp (s', s)), eqn)
                   | (flag, gs_, posEA, vars_, gl_, total, depth,
                      (I.App (u_, s_), s), eqn)
                       -> let (posEA', vars'_, u'_, eqn') =
                            abstractExp
                            (flag, gs_, posEA, vars_, gl_, total, depth,
                             (u_, s), eqn)
                            in let (posEA'', vars''_, s'_, eqn'') =
                                 abstractSpine
                                 (flag, gs_, posEA', vars'_, gl_, total,
                                  depth, (s_, s), eqn')
                                 in (posEA'', vars''_, (I.App (u'_, s'_)),
                                     eqn'')
        and abstractSub' =
          function 
                   | (flag, gs_, epos, vars_, total, I.Shift k) -> begin
                       if k < 0 then
                       raise ((Error "Substitution out of range\n")) else
                       (epos, vars_, (I.Shift (k + total))) end
                   | (flag, gs_, epos, vars_, total, I.Dot (I.Idx k, s))
                       -> let (epos', vars'_, s') =
                            abstractSub' (flag, gs_, epos, vars_, total, s)
                            in (epos', vars'_, (I.Dot ((I.Idx k), s')))
                   | (flag, gs_, epos, vars_, total, I.Dot (I.Exp u_, s))
                       -> let ((ep, _), vars'_, u'_, _) =
                            abstractExp
                            (false, gs_, (epos, 0), vars_, I.null_, total, 0,
                             (u_, I.id), TableParam.trivial_)
                            in let (epos'', vars''_, s') =
                                 abstractSub'
                                 (flag, gs_, ep, vars'_, total, s)
                                 in (epos'', vars''_,
                                     (I.Dot ((I.Exp u'_), s')))
        and abstractDec =
          function 
                   | (gs_, posEA, vars_, gl_, total, depth,
                      (I.Dec (x, v_), s), None)
                       -> let (posEA', vars'_, v'_, eqn) =
                            abstractExp
                            (false, gs_, posEA, vars_, gl_, total, depth,
                             (v_, s), TableParam.trivial_)
                            in (posEA', vars'_, (I.Dec (x, v'_)), eqn)
                   | (gs_, posEA, vars_, gl_, total, depth,
                      (I.Dec (x, v_), s), Some eqn)
                       -> let (posEA', vars'_, v'_, eqn') =
                            abstractExp
                            (true, gs_, posEA, vars_, gl_, total, depth,
                             (v_, s), eqn)
                            in (posEA', vars'_, (I.Dec (x, v'_)), eqn');;
        let rec abstractCtx' =
          function 
                   | (gs_, epos, vars_, total, depth, C.DProg (null_, null_),
                      g'_, eqn) -> (epos, vars_, g'_, eqn)
                   | (gs_, epos, vars_, total, depth, C.DProg
                      (I.Decl (g_, d_), I.Decl (dPool, parameter_)), g'_,
                      eqn)
                       -> let d = IntSyn.ctxLength g_
                            in let ((epos', _), vars'_, d'_, _) =
                                 abstractDec
                                 (gs_, (epos, total), vars_, I.null_, total,
                                  depth - 1, (d_, I.id), None)
                                 in abstractCtx'
                                    (gs_, epos', vars'_, total, depth - 1,
                                     (C.DProg (g_, dPool)),
                                     (I.Decl (g'_, d'_)), eqn)
                   | (gs_, epos, vars_, total, depth, C.DProg
                      (I.Decl (g_, d_), I.Decl (dPool, _)), g'_, eqn)
                       -> let d = IntSyn.ctxLength g_
                            in let ((epos', _), vars'_, d'_, _) =
                                 abstractDec
                                 (gs_, (epos, total), vars_, I.null_, total,
                                  depth - 1, (d_, I.id), None)
                                 in abstractCtx'
                                    (gs_, epos', vars'_, total, depth - 1,
                                     (C.DProg (g_, dPool)),
                                     (I.Decl (g'_, d'_)), eqn);;
        let rec abstractCtx (gs_, epos, vars_, total, depth, dProg) =
          abstractCtx'
          (gs_, epos, vars_, total, depth, dProg, I.null_,
           TableParam.trivial_);;
        let rec makeEVarCtx =
          function 
                   | (gs_, vars_, dEVars_, null_, total) -> dEVars_
                   | (gs_, vars_, dEVars_, I.Decl
                      (k'_, (_, Ev ((I.EVar (_, gx_, vx_, _) as e_)))),
                      total)
                       -> let v'_ = raiseType (gx_, vx_)
                            in let (_, vars'_, v''_, _) =
                                 abstractExp
                                 (false, gs_, (0, 0), vars_, I.null_, 0,
                                  total - 1, (v'_, I.id),
                                  TableParam.trivial_)
                                 in let dEVars'_ =
                                      makeEVarCtx
                                      (gs_, vars'_, dEVars_, k'_, total - 1)
                                      in let dEVars''_ =
                                           (I.Decl
                                            (dEVars'_, (I.Dec (None, v''_))))
                                           in dEVars''_;;
        let rec makeAVarCtx (vars_, dupVars_) =
          let rec avarCtx =
            function 
                     | (vars_, null_, k) -> I.null_
                     | (vars_, I.Decl
                        (k'_, Av
                         ((I.EVar ({ contents = None}, gx_, vx_, _) as e_),
                          d)),
                        k)
                         -> (I.Decl
                             (avarCtx (vars_, k'_, k + 1),
                              (I.ADec
                               ((Some
                                 ((("AVar " ^ (Int.toString k)) ^ "--") ^
                                    (Int.toString d))),
                                d))))
                     | (vars_, I.Decl
                        (k'_, Av ((I.EVar (_, gx_, vx_, _) as e_), d)), k)
                         -> (I.Decl
                             (avarCtx (vars_, k'_, k + 1),
                              (I.ADec
                               ((Some
                                 ((("AVar " ^ (Int.toString k)) ^ "--") ^
                                    (Int.toString d))),
                                d))))
            in avarCtx (vars_, dupVars_, 0);;
        let rec lowerEVar' =
          function 
                   | (x_, g_, (I.Pi ((d'_, _), v'_), s'))
                       -> let d''_ = I.decSub (d'_, s')
                            in let (x'_, u_) =
                                 lowerEVar'
                                 (x_, (I.Decl (g_, d''_)),
                                  Whnf.whnf (v'_, I.dot1 s'))
                                 in (x'_, (I.Lam (d''_, u_)))
                   | (x_, g_, vs'_) -> let x'_ = x_ in (x'_, x'_)
        and lowerEVar1 =
          function 
                   | (x_, I.EVar (r, g_, _, _), ((I.Pi _ as v_), s))
                       -> let (x'_, u_) = lowerEVar' (x_, g_, (v_, s))
                            in (I.EVar
                                (ref ((Some u_)), I.null_, v_, ref []))
                   | (_, x_, _) -> x_
        and lowerEVar =
          function 
                   | (e_, (I.EVar (r, g_, v_, { contents = []}) as x_))
                       -> lowerEVar1 (e_, x_, Whnf.whnf (v_, I.id))
                   | (e_, I.EVar _)
                       -> raise
                          ((Error
                            "abstraction : LowerEVars: Typing ambiguous -- constraint of functional type cannot be simplified"));;
        let rec evarsToSub =
          function 
                   | (null_, s) -> s
                   | (I.Decl
                      (k'_,
                       (_, Ev
                        ((I.EVar
                           (({ contents = None} as i_), gx_, vx_, cnstr) as
                           e_)))),
                      s)
                       -> let v'_ = raiseType (gx_, vx_)
                            in let x_ =
                                 lowerEVar1
                                 (e_, (I.EVar (i_, I.null_, v'_, cnstr)),
                                  Whnf.whnf (v'_, I.id))
                                 in let s' = evarsToSub (k'_, s)
                                      in (I.Dot ((I.Exp x_), s'));;
        let rec avarsToSub =
          function 
                   | (null_, s) -> s
                   | (I.Decl
                      (vars'_, Av ((I.EVar (i_, gx_, vx_, cnstr) as e_), d)),
                      s)
                       -> let s' = avarsToSub (vars'_, s)
                            in let (I.AVar r as x'_) = I.newAVar ()
                                 in (I.Dot
                                     ((I.Exp
                                       ((I.EClo (x'_, (I.Shift (- d)))))),
                                      s'));;
        let rec abstractEVarCtx ((C.DProg (g_, dPool) as dp), p, s) =
          let (gs_, ss, d) = begin
            if ! TableParam.strengthen then
            let w' = Subordinate.weaken (g_, I.targetFam p)
              in let iw = Whnf.invert w'
                   in let g'_ = Whnf.strengthen (iw, g_)
                        in let d' = I.ctxLength g'_ in (g'_, iw, d')
            else (g_, I.id, I.ctxLength g_) end
            in let (k_, dupVars_) =
                 collectCtx ((gs_, ss), dp, (I.null_, I.null_), d)
                 in let (k'_, dupVars'_) =
                      collectExp
                      ((gs_, ss), I.null_, (p, s), k_, dupVars_, true, d)
                      in let epos = I.ctxLength k'_
                           in let apos = I.ctxLength dupVars'_
                                in let total = epos + apos
                                     in let (epos', vars'_, g'_, eqn) =
                                          abstractCtx
                                          ((gs_, ss), epos, I.null_, total,
                                           d, dp)
                                          in let
                                               (posEA'', vars''_, u'_, eqn')
                                               =
                                               abstractExp
                                               (true, (gs_, ss),
                                                (epos', total), vars'_,
                                                I.null_, total, d, (p, s),
                                                eqn)
                                               in let dAVars_ =
                                                    makeAVarCtx
                                                    (vars''_, dupVars'_)
                                                    in let dEVars_ =
                                                         makeEVarCtx
                                                         ((gs_, ss), vars''_,
                                                          I.null_, vars''_,
                                                          0)
                                                         in let s' =
                                                              avarsToSub
                                                              (dupVars'_,
                                                               I.id)
                                                              in let s'' =
                                                                   evarsToSub
                                                                   (vars''_,
                                                                    s')
                                                                   in 
                                                                   let g''_ =
                                                                    reverseCtx
                                                                    (g'_,
                                                                    I.null_)
                                                                    in begin
                                                                    if
                                                                    !
                                                                    TableParam.strengthen
                                                                    then
                                                                    let w' =
                                                                    Subordinate.weaken
                                                                    (g''_,
                                                                    I.targetFam
                                                                    u'_)
                                                                    in 
                                                                    let iw =
                                                                    Whnf.invert
                                                                    w'
                                                                    in 
                                                                    let gs'_
                                                                    =
                                                                    Whnf.strengthen
                                                                    (iw,
                                                                    g''_)
                                                                    in 
                                                                    (gs'_,
                                                                    dAVars_,
                                                                    dEVars_,
                                                                    u'_,
                                                                    eqn',
                                                                    s'') else
                                                                    (g''_,
                                                                    dAVars_,
                                                                    dEVars_,
                                                                    u'_,
                                                                    eqn',
                                                                    s'') end;;
        end;;
    (*
       We write {{K}} for the context of K, where EVars have
       been translated to declarations and their occurrences to BVars.
       For each occurrence of EVar in U, we generate a distinct BVar together with
       a residual constraint. This enforces that the final abstraction of U is
       linear. However, we do not linearize the context G.

       We write {{U}}_K, {{S}}_K for the corresponding translation of an
       expression or spine.

       Just like contexts G, any K is implicitly assumed to be
       well-formed and in dependency order.

       We write  K ||- U  if all EVars in U are collected in K.
       In particular, . ||- U means U contains no EVars.  Similarly,
       for spines K ||- S and other syntactic categories.

       Collection and abstraction raise Error if there are unresolved
       constraints after simplification.
    *);;
    (* eqEVar X Y = B
     where B iff X and Y represent same variable
     *);;
    (* Sun Dec  1 14:04:17 2002 -bp  may raise exception
       if strengthening is applied,i.e. the substitution is not always id! *);;
    (* a few helper functions to manage K *);;
    (* member P K = B option *);;
    (* member P K = B option *);;
    (* member P K = B option *);;
    (* occursInExp (k, U) = DP,

       Invariant:
       If    U in nf
       then  DP = No      iff k does not occur in U
             DP = Maybe   iff k occurs in U some place not as an argument to a Skonst
             DP = Meta    iff k occurs in U and only as arguments to Skonsts
    *);;
    (* no case for Redex, EVar, EClo *);;
    (* no case for FVar *);;
    (* no case for SClo *);;
    (* piDepend ((D,P), V) = Pi ((D,P'), V)
       where P' = Maybe if D occurs in V, P' = No otherwise
    *);;
    (* optimize to have fewer traversals? -cs *);;
    (* pre-Twelf 1.2 code walk Fri May  8 11:17:10 1998 *);;
    (* raiseType (G, V) = {{G}} V

       Invariant:
       If G |- V : L
       then  . |- {{G}} V : L

       All abstractions are potentially dependent.
    *);;
    (* collectExpW ((Gs, ss), Gl, (U, s), K, DupVars, flag) = (K', DupVars')

       Invariant:
       If    G, Gl |- s : G1     G1 |- U : V      (U,s) in whnf
                Gs |- ss : G  (Gs is the strengthened context and ss is the strengthening substitution)

       No circularities in U
             (enforced by extended occurs-check for FVars in Unify)
       and   K' = K, K''
             where K' contains all EVars in (U,s)
       and  DupVars' = DupVars, DupVars''
            where DupVars' contains all duplicates in (U,s)

      if flag = true
        then duplicates of EVars are collected in DupVars
        otherwise no duplicates are collected

      note : 1) we only need to collect duplicate occurrences of EVars
                if we need to linearize the term the EVars occur in.

             2) we do not linearize fgnExp
    *);;
    (* Possible optimization: Calculate also the normal form of the term *);;
    (* should we apply I.dot1(ss) ? Tue Oct 15 21:55:16 2002 -bp *);;
    (* No other cases can occur due to whnf invariant *);;
    (* collectExp (Gss, G, Gl, (U, s), K) = K'
       same as collectExpW  but  (U,s) need not to be in whnf
    *);;
    (* collectSpine (Gss, Gl, (S, s), K, DupVars, flag) = (K', DupVars')

       Invariant:
       If    G, Gl |- s : G1     G1 |- S : V > P
                Gs |- ss : G
       then  K' = K, K'' and DupVars' = DupVars, DupVars''
       where K'' contains all EVars in (S, s)
       and DupVars'' contains all duplicates in (S, s)
     *);;
    (* we have seen X before *);;
    (* case label of
                     Body => collectSub(Gss, Gl, s, K, I.Decl(DupVars, AV(X,d)), flag, d)
                   | TypeLabel =>
                       let
                         val K' = update' (eqEVar X) K
                       in
                         collectSub(Gss, Gl, s, K', DupVars, flag, d)
                       end *);;
    (* since X has occurred before, we do not traverse its type V' *);;
    (*          val V' = raiseType (GX, V)  inefficient! *);;
    (* we have seen X before, i.e. it was already strengthened *);;
    (* -bp this is a possible optimization for the variant case
                   case label of
                   Body => (print ""Collect DupVar\n""; collectSub(Gss, Gl, s, K, I.Decl(DupVars, AV(X, d)), flag, d) )
                 | TypeLabel =>
                    let
                      val _ = print ""TypeLabel\n""
                      val K' = update' (eqEVar X) K
                    in
                      collectSub(Gss, Gl, s, K', DupVars, flag, d)
                    end*);;
    (* val V' = raiseType (GX, V)  inefficient! *);;
    (* ? *);;
    (* equalCtx (Gs, I.id, GX', s) *);;
    (* fully applied *);;
    (* not fully applied *);;
    (* X is fully applied pattern *);;
    (* we have seen X before *);;
    (*
                 case label of
                   Body => collectSub(Gss, Gl, s, K, I.Decl(DupVars, AV(X, d)), flag, d)
                 | TypeLabel =>
                     let
                       val K' = update' (eqEVar X) K
                     in
                       collectSub(Gss, Gl, s, K', DupVars, flag, d)
                     end *);;
    (* since X has occurred before, we do not traverse its type V' *);;
    (* val _ = checkEmpty !cnstrs *);;
    (* inefficient! *);;
    (* case label of
                   Body => collectSub(Gss, Gl, s, K, I.Decl(DupVars, AV(X, d)), flag, d)
                   | TypeLabel =>
                     let
                       val K' = update' (eqEVar X) K
                     in
                       collectSub(Gss, Gl, s, K', DupVars, flag, d)
                     end             *);;
    (* inefficient! *);;
    (* equalCtx (compose'(Gl, G), s, GX, s)  *);;
    (* X is fully applied *);;
    (* X is not fully applied *);;
    (* collectDec (Gss, G, (x:V, s), K, DupVars, flag) = (K', DupVars')

       Invariant:
       If    G |- s : G1     G1 |- V : L
            Gs |- ss : G
       then  K' = K, K'' and DupVars' = DupVars, DupVars''
       where K'' contains all EVars in (V, s)
       and DupVars'' contains all duplicates in (S, s)
    *);;
    (*      val (K',DupVars') =  collectExp (Gss, I.Null, (V, s), K, I.Null, false, d)*);;
    (* collectSub (G, s, K, DupVars, flag) = (K', DupVars)

       Invariant:
       If    G |- s : G1

       then  K' = K, K'' and DupVars' = DupVars, DupVars''
       where K'' contains all EVars in s
       and DupVars'' contains all duplicates in s
    *);;
    (* inefficient? *);;
    (* inefficient? *);;
    (* collectCtx (Gss, G0, G, K) = (K', DupVars)
       Invariant:
       If G0 |- G ctx,
       then G0' = G0,G
       and K' = K, K'' where K'' contains all EVars in G
    *);;
    (* abstractExpW (epos, apos, Vars, Gl, total, depth, (U, s), eqn) = (epos', apos', Vars', U', eqn')
      (abstraction and linearization of existential variables in (U,s))

       U' = {{U[s]}}_(K, Dup)

       Invariant:
       If     G, Gl |- U[s] : V and  U[s] is in whnf
       and   |Gl| = depth
             |Dup, K| = total

       and epos = (total(K) + l) - #replaced expressions in U    (generate no additional constraints)
       and apos = (total(Dup) + + total(K) + l) - #replaced expressions in U
                  (generate additional constraints (avars))

       and Vars'  = Vars, Vars''
           where Vars contains pairs ((label, i), EV X) of all EVars (EV X),
           where label refers to where we have seen the existential variable (typeLabel or body) and
           i corresponds to the bvar-index assigned to X in U[s]

       and   K ~ Vars (we can obtain K from Vars by dropping the first component of
             each pair (_, EV X) in Vars' )

       then   {{Dup}}, {{K}}  ||- U
       and {{Dup}} {{K}} , G, Gl |-  U' : V'
       and eqn' = eqn, eqn'' where eqn'' are residual equations relating between elements
           in {{K}} and {{Dup}}

       and . ||- Pi G. U'  and   U' is in nf

       if flag then linearize U else allow duplicates.

    *);;
    (* X is possibly strengthened ! *);;
    (* X is fully applied *);;
    (* s =/= id, i.e. X is not fully applied *);;
    (*      | abstractExpW (posEA, Vars, Gl, total, depth, (X as I.FgnExp (cs, ops), s), eqn) =  *);;
    (*      let
          val (X, _) = #map(ops) (fn U => abstractExp (posEA, Vars, Gl, total, depth, (U, s), eqn))
        in        abstractFgn (posEA, Vars, Gl, total, depth, X, eqn)
        end
*);;
    (* abstractExp (posEA, Vars, Gl, total, depth, (U, s)) = U'

       same as abstractExpW, but (U,s) need not to be in whnf
    *);;
    (* we have seen X before *);;
    (* enforce linearization *);;
    (* do not enforce linearization -- used for type labels *);;
    (* we see X for the first time *);;
    (* we have seen X before *);;
    (* enforce linearization *);;
    (* (case label of
               Body =>
                 let
                  val _ = print ""abstractEVarNFap -- flag true; we have seen X before\n""
                   val BV = I.BVar(apos + depth)
                   val BV' = I.BVar(i + depth)
                   val BV1 = I.BVar(apos + depth)
                   val (posEA', Vars', S, eqn1) = abstractSub (flag, Gs, (epos, apos - 1), Vars, Gl, total, depth, s, I.Nil, eqn)
                 in
                   (posEA', Vars', I.Root(BV, I.Nil), TableParam.Unify(Gl, I.Root(BV', S), I.Root(BV1, I.Nil ), eqn1))
                 end
              | TyeLabel =>
                 let
                   val Vars' = update (eqEVar X) Vars
                   val (posEA', Vars'', S, eqn1) = abstractSub (flag, Gs, (epos, apos), Vars', Gl, total, depth, s, I.Nil, eqn)
                 in
                   (posEA', Vars'', I.Root(I.BVar(i + depth), S), eqn1)
                 end) *);;
    (* do not enforce linearization -- used for type labels *);;
    (* we have not seen X before *);;
    (* enforce linearization since X is not fully applied *);;
    (* do not enforce linearization -- used for type labels *);;
    (* abstractSub (flag, Gs, posEA, Vars, Gl, total, depth, s, S, eqn) = (posEA', Vars', S', eqn')

       (implicit raising)
       (for posEA, Vars, eqn explanation see above)

       let K* = K, Dup

       S' = {{s}}_K* @@ S

       Invariant:
       If    G, Gl |- s : G1
       and  |Gl| = depth

       and   {{Dup}} {{K}} ||- s
       then {{Dup}} {{K}}, G, Gl |- S' : {G1}.W > W   (for some W)
       and  . ||- S'
    *);;
    (* k = depth *);;
    (* abstractSpine (flag, Gs, posEA, Vars, Gl, total, depth, (S, s), eqn) = (posEA', Vars', S', eqn')
       where S' = {{S[s]}}_K*   and K* = K, Dup

       Invariant:
       If   Gl, G |- s : G1     G1 |- S : V > P
       and  K* ||- S
       and  |G| = depth

       then {{K*}}, G, G |- S' : V' > P'
       and  . ||- S'
    *);;
    (* abstractSub' (flag, Gs, epos, K, Gl, total, s) = (epos', K', s')      (implicit raising)

        Invariant:
        If   G |- s : G1
       and  |G| = depth
       and  K ||- s
       and {{K}}, G |- {{s}}_K : G1
       then Gs, G |- s' : G1    where  s' == {{s}}_K

         *);;
    (* abstractDec (Gs, posEA, Vars, Gl, total, depth, (x:V, s)) = (posEA', Vars', x:V')
       where V = {{V[s]}}_K*

       Invariant:
       If   G |- s : G1     G1 |- V : L
       and  K* ||- V
       and  |G| = depth

       then {{K*}}, G |- V' : L
       and  . ||- V'
    *);;
    (*      val (posEA', Vars', V', _) = abstractExp (false, Gs, posEA, Vars, Gl, total, depth, (V, s), TableParam.Trivial)*);;
    (*      val (posEA', Vars', V', _) = abstractExp (false, Gs, posEA, Vars, Gl, total, depth, (V, s), TableParam.Trivial)*);;
    (* abstractCtx (Gs, epos, K, total, depth, C.DProg(G,dPool)) = (epos', K', G')
       where G' = {{G}}_K

       Invariants:
       If K ||- G
       and |G| = depth
       then {{K}} |- G' ctx
       and . ||- G'
       and epos = current epos

       note: we will linearize all dynamic assumptions in G.
    *);;
    (*        let
          val d = IntSyn.ctxLength (G)
          val ((epos', _), Vars', D', eqn') = abstractDec (Gs, (epos, total), Vars, I.Null, total , depth - 1, (D, I.id), SOME(eqn))
        in
          abstractCtx' (Gs, epos', Vars', total, depth - 1, C.DProg(G, dPool), I.Decl (G', D'), eqn')
        end
*);;
    (* makeEVarCtx (Gs, Kall, D, K, eqn) = G'  *);;
    (* add case for foreign expressions ? *);;
    (* lowerEVar' (G, V[s]) = (X', U), see lowerEVar *);;
    (* lowerEVar1 (X, V[s]), V[s] in whnf, see lowerEVar *);;
    (* lowerEVar1 (X, I.EVar (r, G, _, _), (V as I.Pi _, s)) = *);;
    (* lowerEVar (X) = X'

       Invariant:
       If   G |- X : {{G'}} P
            X not subject to any constraints
       then G, G' |- X' : P

       Effect: X is instantiated to [[G']] X' if G' is empty
               otherwise X = X' and no effect occurs.
    *);;
    (* It is not clear if this case can happen *);;
    (* pre-Twelf 1.2 code walk, Fri May  8 11:05:08 1998 *);;
    (* evarsToSub (K, s') = s
      Invariant:
      if K = EV Xn ... EV X2, EV X1
        then
        s = X1 . X2 . ... s'
     *);;
    (* redundant ? *);;
    (* evarsToSub (K, s') = s
      Invariant:
      if K = AV Xn ... AV X2, EV X1
        then
        s = X1 . X2 . ... s'
     *);;
    (* abstractEVarCtx (G, p, s) = (G', D', U', s')

     if G |- p[s] and s contains free variables X_n .... X_1
     then
       D' |- Pi  G' . U'
       where D' is the abstraction over the free vars X_n .... X_1

       and s' is a substitution the free variables
            X_n .... X_1, s.t.

       . |- s' : D'

       . |- (Pi G' .U' )[s']  is equivalent to . |- Pi G . p[s]

       Note: G' and U' are possibly strengthened
   *);;
    (* K ||- G i.e. K contains all EVars in G *);;
    (* DupVars' , K' ||- p[s]  i.e. K' contains all EVars in (p,s) and G and
                                         DupVars' contains all duplicate EVars p[s] *);;
    (* {{G}}_Vars' , i.e. abstract over the existential variables in G*);;
    (* = 0 *);;
    (* abstract over existential variables in p[s] and linearize the expression *);;
    (* depth *);;
    (* note: depth will become negative during makeEVarCtx *);;
    let abstractEVarCtx = abstractEVarCtx;;
    (* abstractAnswSub s = (D', s')

   if  |- s : Delta' and s may contain free variables and
     D |- Pi G. U  and  |- s : D and  |- (Pi G . U)[s]
    then

    D' |- s' : D   where D' contains all the
    free variables from s
   *);;
    let abstractAnswSub =
      function 
               | s
                   -> let (k_, _) =
                        collectSub
                        ((I.null_, I.id), I.null_, s, I.null_, I.null_,
                         false, 0)
                        in let epos = I.ctxLength k_
                             in let ((_, vars_, s')(*0 *)) =
                                  abstractSub'
                                  (false, (I.null_, I.id), epos, I.null_,
                                   epos, s)
                                  (* total *)
                                  in let dEVars_ =
                                       makeEVarCtx
                                       ((I.null_, I.id), vars_, I.null_,
                                        vars_, 0)
                                       in let s1' =
                                            ctxToEVarSub (dEVars_, I.id)
                                            in (dEVars_, s')
                                            (* no linearization for answer substitution *);;
    let raiseType = function 
                             | (g_, u_) -> raiseType (g_, u_);;
    end;;
(*! sharing Conv.IntSyn = IntSyn' !*);;
(*! structure TableParam : TABLEPARAM !*);;
(*! sharing TableParam.IntSyn = IntSyn' !*);;
(* functor AbstractTabled *);;