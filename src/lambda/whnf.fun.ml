open! Basis;;
(* Weak Head-Normal Forms *);;
(* Author: Frank Pfenning, Carsten Schuermann *);;
(* Modified: Roberto Virga *);;
module Whnf() : WHNF =
  struct
    (*! structure IntSyn = IntSyn' !*);;
    (*
     Weak Head-Normal Form (whnf)

     whnf ::= (L, s) | (Pi DP. U, s) | (Root (#k(b), S))
            | (Root(n,S), id) | (Root(c,S), id) | (Root(d,S), id) | (Root(F[s'], S), id)
            | (Root(fgnC,S), id) where fgnC is a foreign constant
            | (Lam D. U, s) | (X, s) where X is uninstantiated, X of base type
                                     during type reconstruction, X might have variable type
            | (FgnExp, id) where FgnExp is a foreign expression

     Normal Form (nf)

        UA ::= L | Pi (DA,P). UA
             | Root(n,SA) | Root(c,SA) | Root(d,SA) | Root(fgnC,SA) | Root (#k(b), S)
             | Lam DA. UA | FgnExp
        DA ::= x:UA
        SA ::= Nil | App (UA, SA)

     Existential Normal Form (enf)

     Existential normal forms are like normal forms, but also allows
     X[s] where X is uninstantiated with no particular restriction on s
     or type of X.

     An existential normal form is a hereditary weak head-normal form.
  *);;
    open!
      struct
        open IntSyn;;
        exception Eta ;;
        let rec etaContract =
          function 
                   | (Root (BVar k, s_), s, n)
                       -> begin
                          match bvarSub (k, s)
                          with 
                               | Idx k' -> begin
                                   if k' > n then
                                   begin
                                     etaContract' (s_, s, n);k' - n
                                     end
                                   else raise Eta end
                               | _ -> raise Eta
                          end
                   | (Lam (d_, u_), s, n) -> etaContract (u_, dot1 s, n + 1)
                   | (EClo (u_, s'), s, n)
                       -> etaContract (u_, comp (s', s), n)
                   | (EVar ({ contents = Some u_}, _, _, _), s, n)
                       -> etaContract (u_, s, n)
                   | (AVar { contents = Some u_}, s, n)
                       -> etaContract (u_, s, n)
                   | _ -> raise Eta
        and etaContract' =
          function 
                   | (Nil, s, 0) -> ()
                   | (App (u_, s_), s, n) -> begin
                       if (etaContract (u_, s, 0)) = n then
                       etaContract' (s_, s, n - 1) else raise Eta end
                   | (SClo (s_, s'), s, n)
                       -> etaContract' (s_, comp (s', s), n)
                   | _ -> raise Eta;;
        let rec dotEta =
          function 
                   | ((Idx _ as ft_), s) -> (Dot (ft_, s))
                   | ((Exp u_ as ft_), s)
                       -> let ft'_ =
                            try (Idx (etaContract (u_, id, 0)))
                            with 
                                 | Eta -> ft_
                            in (Dot (ft'_, s))
                   | ((Undef as ft_), s) -> (Dot (ft_, s));;
        let rec appendSpine =
          function 
                   | ((Nil, s1), ss2_) -> (SClo ss2_)
                   | ((App (u1_, s1_), s1), ss2_)
                       -> (App
                           ((EClo (u1_, s1)), appendSpine ((s1_, s1), ss2_)))
                   | ((SClo (s1_, s1'), s1), ss2_)
                       -> appendSpine ((s1_, comp (s1', s1)), ss2_);;
        let rec whnfRedex =
          function 
                   | (us_, (SClo (s_, s2'), s2))
                       -> whnfRedex (us_, (s_, comp (s2', s2)))
                   | (((Root r_, s1) as us_), (Nil, s2)) -> us_
                   | ((Root (h1_, s1_), s1), (s2_, s2))
                       -> ((Root (h1_, appendSpine ((s1_, s1), (s2_, s2)))),
                           id)
                   | ((Lam (_, u1_), s1), (App (u2_, s_), s2))
                       -> whnfRedex
                          (whnf (u1_, dotEta (frontSub ((Exp u2_), s2), s1)),
                           (s_, s2))
                   | (((Lam _, s1) as us_), _) -> us_
                   | (((EVar _, s1) as us_), (Nil, s2)) -> us_
                   | ((((EVar _ as x_), s1) as us_), ss2_)
                       -> begin
                            lowerEVar x_;whnfRedex (whnf us_, ss2_)
                            end
                   | (((AVar { contents = Some u_}, s1) as us_), ss2_)
                       -> whnfRedex ((u_, s1), ss2_)
                   | (((AVar { contents = None}, s1) as us_), ss2_) -> us_
                   | (((FgnExp _, _) as us_), _) -> us_
                   | (((Uni _, s1) as us_), _) -> us_
                   | (((Pi _, s1) as us_), _) -> us_
        and lowerEVar' =
          function 
                   | (g_, (Pi ((d'_, _), v'_), s'))
                       -> let d''_ = decSub (d'_, s')
                            in let (x'_, u_) =
                                 lowerEVar'
                                 ((Decl (g_, d''_)),
                                  whnfExpandDef (v'_, dot1 s'))
                                 in (x'_, (Lam (d''_, u_)))
                   | (g_, vs'_)
                       -> let x'_ = newEVar (g_, (EClo vs'_)) in (x'_, x'_)
        and lowerEVar1 =
          function 
                   | (EVar (r, g_, _, _), ((Pi _, _) as vs_))
                       -> let (x'_, u_) = lowerEVar' (g_, vs_)
                            in let _ = r := ((Some u_)) in x'_
                   | (x_, _) -> x_
        and lowerEVar =
          function 
                   | (EVar (r, g_, v_, { contents = []}) as x_)
                       -> lowerEVar1 (x_, whnfExpandDef (v_, id))
                   | EVar _
                       -> raise
                          ((Error
                            "Typing ambiguous -- constraint of functional type cannot be simplified"))
        and whnfRoot =
          function 
                   | ((BVar k, s_), s)
                       -> begin
                          match bvarSub (k, s)
                          with 
                               | Idx k
                                   -> ((Root ((BVar k), (SClo (s_, s)))), id)
                               | Exp u_ -> whnfRedex (whnf (u_, id), (s_, s))
                          end
                   | ((Proj ((Bidx _ as b_), i), s_), s)
                       -> begin
                          match blockSub (b_, s)
                          with 
                               | (Bidx k as b'_)
                                   -> ((Root
                                        ((Proj (b'_, i)), (SClo (s_, s)))),
                                       id)
                               | (LVar _ as b'_)
                                   -> whnfRoot
                                      (((Proj (b'_, i)), (SClo (s_, s))), id)
                               | Inst l_
                                   -> whnfRedex
                                      (whnf (List.nth (l_, i - 1), id),
                                       (s_, s))
                          end
                   | ((Proj (LVar ({ contents = Some b_}, sk, (l, t)), i),
                       s_),
                      s)
                       -> whnfRoot
                          (((Proj (blockSub (b_, comp (sk, s)), i)),
                            (SClo (s_, s))),
                           id)
                   | ((Proj ((LVar (r, sk, (l, t)) as l_), i), s_), s)
                       -> ((Root
                            ((Proj ((LVar (r, comp (sk, s), (l, t))), i)),
                             (SClo (s_, s)))),
                           id)
                   | ((FVar (name, v_, s'), s_), s)
                       -> ((Root
                            ((FVar (name, v_, comp (s', s))), (SClo (s_, s)))),
                           id)
                   | ((NSDef d, s_), s)
                       -> whnfRedex (whnf (IntSyn.constDef d, id), (s_, s))
                   | ((h_, s_), s) -> ((Root (h_, (SClo (s_, s)))), id)
        and whnf =
          function 
                   | ((Uni _ as u_), s) -> (u_, s)
                   | ((Pi _ as u_), s) -> (u_, s)
                   | (Root r_, s) -> whnfRoot (r_, s)
                   | (Redex (u_, s_), s) -> whnfRedex (whnf (u_, s), (s_, s))
                   | ((Lam _, s) as us_) -> us_
                   | (AVar { contents = Some u_}, s) -> whnf (u_, s)
                   | ((AVar _, s) as us_) -> us_
                   | (EVar ({ contents = Some u_}, _, _, _), s)
                       -> whnf (u_, s)
                   | ((EVar (r, _, Root _, _), s) as us_) -> us_
                   | ((EVar (r, _, Uni _, _), s) as us_) -> us_
                   | (((EVar (r, _, v_, _) as x_), s) as us_)
                       -> begin
                          match whnf (v_, id)
                          with 
                               | (Pi _, _) -> begin
                                                lowerEVar x_;whnf us_
                                                end
                               | _ -> us_
                          end
                   | (EClo (u_, s'), s) -> whnf (u_, comp (s', s))
                   | ((FgnExp _, Shift 0) as us_) -> us_
                   | ((FgnExp csfe, s) as us_)
                       -> (FgnExpStd.Map.apply
                           csfe
                           (function 
                                     | u_ -> (EClo (u_, s))),
                           id)
        and expandDef (Root (Def d, s_), s) =
          whnfRedex (whnf (constDef d, id), (s_, s))
        and whnfExpandDefW =
          function 
                   | ((Root (Def _, _), _) as us_)
                       -> whnfExpandDefW (expandDef us_)
                   | us_ -> us_
        and whnfExpandDef us_ = whnfExpandDefW (whnf us_);;
        let rec newLoweredEVarW =
          function 
                   | (g_, (Pi ((d_, _), v_), s))
                       -> let d'_ = decSub (d_, s)
                            in (Lam
                                (d'_,
                                 newLoweredEVar
                                 ((Decl (g_, d'_)), (v_, dot1 s))))
                   | (g_, vs_) -> newEVar (g_, (EClo vs_))
        and newLoweredEVar (g_, vs_) =
          newLoweredEVarW (g_, whnfExpandDef vs_);;
        let rec newSpineVarW =
          function 
                   | (g_, (Pi ((Dec (_, va_), _), vr_), s))
                       -> let x_ = newLoweredEVar (g_, (va_, s))
                            in (App
                                (x_,
                                 newSpineVar
                                 (g_, (vr_, dotEta ((Exp x_), s)))))
                   | (g_, _) -> Nil
        and newSpineVar (g_, vs_) = newSpineVarW (g_, whnfExpandDef vs_);;
        let rec spineToSub =
          function 
                   | (Nil, s) -> s
                   | (App (u_, s_), s)
                       -> spineToSub (s_, dotEta ((Exp u_), s));;
        let rec inferSpine =
          function 
                   | ((Nil, _), vs_) -> vs_
                   | ((SClo (s_, s'), s), vs_)
                       -> inferSpine ((s_, comp (s', s)), vs_)
                   | ((App (u_, s_), s1), (Pi (_, v2_), s2))
                       -> inferSpine
                          ((s_, s1),
                           whnfExpandDef
                           (v2_, (Dot ((Exp ((EClo (u_, s1)))), s2))));;
        let rec inferCon =
          function 
                   | Const cid -> constType cid
                   | Skonst cid -> constType cid
                   | Def cid -> constType cid;;
        let rec etaExpand' =
          function 
                   | (u_, (Root _, s)) -> u_
                   | (u_, (Pi ((d_, _), v_), s))
                       -> (Lam
                           (decSub (d_, s),
                            etaExpand'
                            ((Redex
                              ((EClo (u_, shift)),
                               (App ((Root ((BVar 1), Nil)), Nil)))),
                             whnfExpandDef (v_, dot1 s))));;
        let rec etaExpandRoot ((Root (h_, s_) as u_)) =
          etaExpand' (u_, inferSpine ((s_, id), (inferCon h_, id)));;
        let rec whnfEta (us_, vs_) = whnfEtaW (whnf us_, whnf vs_)
        and whnfEtaW =
          function 
                   | ((_, (Root _, _)) as usVs_) -> usVs_
                   | (((Lam _, _), (Pi _, _)) as usVs_) -> usVs_
                   | ((u_, s1), ((Pi ((d_, p_), v_), s2) as vs2_))
                       -> (((Lam
                             (decSub (d_, s2),
                              (Redex
                               ((EClo (u_, comp (s1, shift))),
                                (App ((Root ((BVar 1), Nil)), Nil)))))),
                            id),
                           vs2_);;
        let rec normalizeExp us_ = normalizeExpW (whnf us_)
        and normalizeExpW =
          function 
                   | ((Uni l_ as u_), s) -> u_
                   | (Pi (dp_, u_), s)
                       -> (Pi
                           (normalizeDecP (dp_, s),
                            normalizeExp (u_, dot1 s)))
                   | ((Root (h_, s_) as u_), s)
                       -> (Root (h_, normalizeSpine (s_, s)))
                   | (Lam (d_, u_), s)
                       -> (Lam
                           (normalizeDec (d_, s), normalizeExp (u_, dot1 s)))
                   | ((EVar _, s) as us_) -> (EClo us_)
                   | (FgnExp csfe, s)
                       -> FgnExpStd.Map.apply
                          csfe
                          (function 
                                    | u_ -> normalizeExp (u_, s))
                   | ((AVar { contents = Some u_}, s) as us_)
                       -> normalizeExpW (u_, s)
                   | ((AVar _, s) as us_)
                       -> begin
                            print "Normalize  AVAR\n";raise ((Error ""))
                            end
        and normalizeSpine =
          function 
                   | (Nil, s) -> Nil
                   | (App (u_, s_), s)
                       -> (App
                           (normalizeExp (u_, s), normalizeSpine (s_, s)))
                   | (SClo (s_, s'), s) -> normalizeSpine (s_, comp (s', s))
        and normalizeDec =
          function 
                   | (Dec (xOpt, v_), s)
                       -> (Dec (xOpt, normalizeExp (v_, s)))
                   | (BDec (xOpt, (c, t)), s)
                       -> (BDec (xOpt, (c, normalizeSub (comp (t, s)))))
        and normalizeDecP ((d_, p_), s) = (normalizeDec (d_, s), p_)
        and normalizeSub =
          function 
                   | (Shift _ as s) -> s
                   | Dot ((Idx _ as ft_), s) -> (Dot (ft_, normalizeSub s))
                   | Dot (Exp u_, s)
                       -> dotEta
                          ((Exp (normalizeExp (u_, id))), normalizeSub s);;
        let rec normalizeCtx =
          function 
                   | Null -> Null
                   | Decl (g_, d_)
                       -> (Decl (normalizeCtx g_, normalizeDec (d_, id)));;
        let rec invert s =
          let rec lookup =
            function 
                     | (n, Shift _, p) -> None
                     | (n, Dot (Undef, s'), p) -> lookup (n + 1, s', p)
                     | (n, Dot (Idx k, s'), p) -> begin
                         if k = p then (Some n) else lookup (n + 1, s', p)
                         end
            in let rec invert'' =
                 function 
                          | (0, si) -> si
                          | (p, si)
                              -> begin
                                 match lookup (1, s, p)
                                 with 
                                      | Some k
                                          -> invert''
                                             (p - 1, (Dot ((Idx k), si)))
                                      | None
                                          -> invert''
                                             (p - 1, (Dot (Undef, si)))
                                 end
                 in let rec invert' =
                      function 
                               | (n, Shift p) -> invert'' (p, (Shift n))
                               | (n, Dot (_, s')) -> invert' (n + 1, s')
                      in invert' (0, s);;
        let rec strengthen =
          function 
                   | (Shift n, Null) -> Null
                   | (Dot (Idx k, t), Decl (g_, d_))
                       -> let t' = comp (t, invShift)
                            in (Decl (strengthen (t', g_), decSub (d_, t')))
                   | (Dot (Undef, t), Decl (g_, d_)) -> strengthen (t, g_)
                   | (Shift n, g_)
                       -> strengthen
                          ((Dot ((Idx (n + 1)), (Shift (n + 1)))), g_);;
        let rec isId' =
          function 
                   | (Shift k, k') -> k = k'
                   | (Dot (Idx n, s'), k')
                       -> (n = k') && (isId' (s', k' + 1))
                   | _ -> false;;
        let rec isId s = isId' (s, 0);;
        let rec cloInv (u_, w) = (EClo (u_, invert w));;
        let rec compInv (s, w) = comp (s, invert w);;
        let rec isPatSub =
          function 
                   | Shift k -> true
                   | Dot (Idx n, s)
                       -> let rec checkBVar =
                            function 
                                     | Shift k -> n <= k
                                     | Dot (Idx n', s)
                                         -> (n <> n') && (checkBVar s)
                                     | Dot (Undef, s) -> checkBVar s
                                     | _ -> false
                            in (checkBVar s) && (isPatSub s)
                   | Dot (Undef, s) -> isPatSub s
                   | _ -> false;;
        let rec mkPatSub =
          function 
                   | (Shift k as s) -> s
                   | Dot (Idx n, s)
                       -> let s' = mkPatSub s
                            in let rec checkBVar =
                                 function 
                                          | Shift k -> n <= k
                                          | Dot (Idx n', s')
                                              -> (n <> n') && (checkBVar s')
                                          | Dot (Undef, s') -> checkBVar s'
                                 in let _ = checkBVar s'
                                      in (Dot ((Idx n), s'))
                   | Dot (Undef, s) -> (Dot (Undef, mkPatSub s))
                   | Dot (Exp u_, s)
                       -> let (u'_, t') = whnf (u_, id)
                            in let k = etaContract (u'_, t', 0)
                                 in (Dot ((Idx k), mkPatSub s))
                   | _ -> raise Eta;;
        let rec makePatSub s = try (Some (mkPatSub s)) with 
                                                            | Eta -> None;;
        end;;
    (* exception Undefined *);;
    (* etaContract (U, s, n) = k'

       Invariant:
       if   G, V1, .., Vn |- s : G1  and  G1 |- U : V
       then if   lam V1...lam Vn. U[s] =eta*=> k
            then k' = k
            and  G |- k' : Pi V1...Pi Vn. V [s]
            else Eta is raised
              (even if U[s] might be eta-reducible to some other expressions).
    *);;
    (* optimization(?): quick check w/o substitution first *);;
    (* Should fail: (c@S), (d@S), (F@S), X *);;
    (* Not treated (fails): U@S *);;
    (* Could weak head-normalize for more thorough checks *);;
    (* Impossible: L, Pi D.V *);;
    (* etaContract' (S, s, n) = R'

       Invariant:
       If  G |- s : G1    and  G1 |- S : V > W
       then if   S[s] =eta*=> n ; n-1 ; ... ; 1 ; Nil
            then ()
       else Eta is raised
    *);;
    (* dotEta (Ft, s) = s'

       Invariant:
       If   G |- s : G1, V  and G |- Ft : V [s]
       then Ft  =eta*=>  Ft1
       and  s' = Ft1 . s
       and  G |- s' : G1, V
    *);;
    (* appendSpine ((S1, s1), (S2, s2)) = S'

       Invariant:
       If    G |- s1 : G1   G1 |- S1 : V1' > V1
       and   G |- s2 : G2   G2 |- S2 : V2  > V2'
       and   G |- V1 [s1] == V2 [s2]
       then  G |- S' : V1' [s1] > V2' [s2]
    *);;
    (* whnfRedex ((U, s1), (S, s2)) = (U', s')

       Invariant:
       If    G |- s1 : G1   G1 |- U : V1,   (U,s1) whnf
             G |- s2 : G2   G2 |- S : V2 > W2
             G |- V1 [s1] == V2 [s2] == V : L
       then  G |- s' : G',  G' |- U' : W'
       and   G |- W'[s'] == W2[s2] == W : L
       and   G |- U'[s'] == (U[s1] @ S[s2]) : W
       and   (U',s') whnf

       Effects: EVars may be lowered to base type.
    *);;
    (* S2 = App _, only possible if term is not eta-expanded *);;
    (* S2[s2] = Nil *);;
    (* Ss2 must be App, since prior cases do not apply *);;
    (* lowerEVar X results in redex, optimize by unfolding call to whnfRedex *);;
    (* Uni and Pi can arise after instantiation of EVar X : K *);;
    (* S2[s2] = Nil *);;
    (* S2[s2] = Nil *);;
    (* Other cases impossible since (U,s1) whnf *);;
    (* lowerEVar' (G, V[s]) = (X', U), see lowerEVar *);;
    (* lowerEVar1 (X, V[s]), V[s] in whnf, see lowerEVar *);;
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
    (* whnfRoot ((H, S), s) = (U', s')

       Invariant:
       If    G |- s : G1      G1 |- H : V
                              G1 |- S : V > W
       then  G |- s' : G'     G' |- U' : W'
       and   G |- W [s] = W' [s'] : L

       Effects: EVars may be instantiated when lowered
    *);;
    (* Undef should be impossible *);;
    (* could blockSub (B, s) return instantiated LVar ? *);;
    (* Sat Dec  8 13:43:17 2001 -fp !!! *);;
    (* yes Thu Dec 13 21:48:10 2001 -fp !!! *);;
    (* was: (Root (Proj (blockSub (B, s), i), SClo (S, s)), id) *);;
    (* r = ref NONE *);;
    (* scary: why is comp(sk, s) = ^n ?? -fp July 22, 2010, -fp -cs *);;
    (* was:
         (Root (Proj (LVar (r, comp (sk, s), (l, comp(t, s))), i), SClo (S, s)), id)
         Jul 22, 2010 -fp -cs
         *);;
    (* do not compose with t due to globality invariant *);;
    (* Thu Dec  6 20:34:30 2001 -fp !!! *);;
    (* was: (Root (Proj (L, i), SClo (S, s)), id) *);;
    (* going back to first version, because globality invariant *);;
    (* no longer satisfied Wed Nov 27 09:49:58 2002 -fp *);;
    (* Undef and Exp should be impossible by definition of substitution -cs *);;
    (* whnf (U, s) = (U', s')

       Invariant:
       If    G |- s : G'    G' |- U : V
       then  G |- s': G''   G''|- U' : V'
       and   G |- V [s] == V' [s'] == V'' : L
       and   G |- U [s] == U' [s'] : V''
       and   (U', s') whnf
    *);;
    (*
       Possible optimization :
         Define whnf of Root as (Root (n , S [s]), id)
         Fails currently because appendSpine does not necessairly return a closure  -cs
         Advantage: in unify, abstract... the spine needn't be treated under id, but under s
    *);;
    (* simple optimization (C@S)[id] = C@S[id] *);;
    (* applied in Twelf 1.1 *);;
    (* Sat Feb 14 20:53:08 1998 -fp *);;
    (*      | whnf (Us as (Root _, Shift (0))) = Us*);;
    (* commented out, because non-strict definitions slip
         Mon May 24 09:50:22 EDT 1999 -cs  *);;
    (* | whnf (Us as (EVar _, s)) = Us *);;
    (* next two avoid calls to whnf (V, id), where V is type of X *);;
    (* possible opt: call lowerEVar1 *);;
    (* expandDef (Root (Def (d), S), s) = (U' ,s')

       Invariant:
       If    G |- s : G1     G1 |- S : V > W            ((d @ S), s) in whnf
                             .  |- d = U : V'
       then  G |- s' : G'    G' |- U' : W'
       and   G |- V' == V [s] : L
       and   G |- W' [s'] == W [s] == W'' : L
       and   G |- (U @ S) [s] == U' [s'] : W'
       and   (U', s') in whnf
    *);;
    (* why the call to whnf?  isn't constDef (d) in nf? -kw *);;
    (* inferSpine ((S, s1), (V, s2)) = (V', s')

       Invariant:
       If  G |- s1 : G1  and  G1 |- S : V1 > V1'
       and G |- s2 : G2  and  G2 |- V : L,  (V, s2) in whnf
       and G |- S[s1] : V[s2] > W  (so V1[s1] == V[s2] and V1[s1] == W)
       then G |- V'[s'] = W
    *);;
    (* FIX: this is almost certainly mis-design -kw *);;
    (* inferCon (C) = V  if C = c or C = d or C = sk and |- C : V *);;
    (* FIX: this is almost certainly mis-design -kw *);;
    (* etaExpand' (U, (V,s)) = U'

       Invariant :
       If    G |- U : V [s]   (V,s) in whnf
       then  G |- U' : V [s]
       and   G |- U == U' : V[s]
       and   (U', id) in whnf and U' in head-eta-long form
    *);;
    (* quite inefficient -cs *);;
    (* FIX: this is almost certainly mis-design -kw *);;
    (* etaExpandRoot (Root(H, S)) = U' where H = c or H = d

       Invariant:
       If   G |- H @ S : V  where H = c or H = d
       then G |- U' : V
       and  G |- H @ S == U'
       and (U',id) in whnf and U' in head-eta-long form
    *);;
    (* FIX: this is almost certainly mis-design -kw *);;
    (* whnfEta ((U, s1), (V, s2)) = ((U', s1'), (V', s2)')

       Invariant:
       If   G |- s1 : G1  G1 |- U : V1
       and  G |- s2 : G2  G2 |- V : L
       and  G |- V1[s1] == V[s2] : L

       then G |- s1' : G1'  G1' |- U' : V1'
       and  G |- s2' : G2'  G2' |- V' : L'
       and  G |- V1'[s1'] == V'[s2'] : L
       and (U', s1') is in whnf
       and (V', s2') is in whnf
       and (U', s1') == Lam x.U'' if V[s2] == Pi x.V''

       Similar to etaExpand', but without recursive expansion
    *);;
    (* FIX: this is almost certainly mis-design -kw *);;
    (* Invariant:

       normalizeExp (U, s) = U'
       If   G |- s : G' and G' |- U : V
       then U [s] = U'
       and  U' in existential normal form

       If (U, s) contain no existential variables,
       then U' in normal formal
    *);;
    (* s = id *);;
    (* dead code -fp *);;
    (* pre-Twelf 1.2 code walk Fri May  8 11:37:18 1998 *);;
    (* not any more --cs Wed Jun 19 13:59:56 EDT 2002 *);;
    (* changed to obtain pattern substitution if possible *);;
    (* Sat Dec  7 16:58:09 2002 -fp *);;
    (* Dot (Exp (normalizeExp (U, id)), normalizeSub s) *);;
    (* invert s = s'

       Invariant:
       If   G |- s : G'    (and s patsub)
       then G' |- s' : G
       s.t. s o s' = id
    *);;
    (* strengthen (t, G) = G'

       Invariant:
       If   G'' |- t : G     and t strsub 
       then G' |- t : G  and G' subcontext of G
    *);;
    (* = 0 *);;
    (* k = 1 *);;
    (* G |- D dec *);;
    (* G' |- t' : G *);;
    (* G' |- D[t'] dec *);;
    (* isId s = B

       Invariant:
       If   G |- s: G', s weakensub
       then B holds
            iff s = id, G' = G
    *);;
    (* cloInv (U, w) = U[w^-1]

       Invariant:
       If G |- U : V
          G |- w : G'  w weakening subst
          U[w^-1] defined (without pruning or constraints)

       then G' |- U[w^-1] : V[w^-1]
       Effects: None
    *);;
    (* cloInv (s, w) = s o w^-1

       Invariant:
       If G |- s : G1
          G |- w : G2  s weakening subst
          s o w^-1 defined (without pruning or constraints)

       then G2 |- s o w^-1 : G1
       Effects: None
    *);;
    (* functions previously in the Pattern functor *);;
    (* eventually, they may need to be mutually recursive with whnf *);;
    (* isPatSub s = B

       Invariant:
       If    G |- s : G'
       and   s = n1 .. nm ^k
       then  B iff  n1, .., nm pairwise distinct
               and  ni <= k or ni = _ for all 1 <= i <= m
    *);;
    (* Try harder, due to bug somewhere *);;
    (* Sat Dec  7 17:05:02 2002 -fp *);;
    (* false *);;
    (* below does not work, because the patSub is lost *);;
    (*
          let val (U', s') = whnf (U, id)
          in
            isPatSub (Dot (Idx (etaContract (U', s', 0)), s))
            handle Eta => false
          end
      | isPatSub _ = false
      *);;
    (* makePatSub s = SOME(s') if s is convertible to a patSub
                      NONE otherwise

       Invariant:
       If    G |- s : G'
       and   s = n1 .. nm ^k
       then  B iff  n1, .., nm pairwise distinct
               and  ni <= k or ni = _ for all 1 <= i <= m
    *);;
    (* may raise Eta *);;
    let isPatSub = isPatSub;;
    let makePatSub = makePatSub;;
    let dotEta = dotEta;;
    exception Eta = Eta;;
    let etaContract = function 
                               | u_ -> etaContract (u_, id, 0);;
    let whnf = whnf;;
    let expandDef = expandDef;;
    let whnfExpandDef = whnfExpandDef;;
    let etaExpandRoot = etaExpandRoot;;
    let whnfEta = whnfEta;;
    let lowerEVar = lowerEVar;;
    let newLoweredEVar = newLoweredEVar;;
    let newSpineVar = newSpineVar;;
    let spineToSub = spineToSub;;
    let normalize = normalizeExp;;
    let normalizeDec = normalizeDec;;
    let normalizeCtx = normalizeCtx;;
    let invert = invert;;
    let strengthen = strengthen;;
    let isId = isId;;
    let cloInv = cloInv;;
    let compInv = compInv;;
    end;;
(*! structure IntSyn' : INTSYN !*);;
(* functor Whnf *);;