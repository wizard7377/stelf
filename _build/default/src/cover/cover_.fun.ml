open! Basis;;
(* Coverage Checking *);;
(* Author: Frank Pfenning *);;
module Cover(Cover__0: sig
                       module Global : GLOBAL
                       module Whnf : WHNF
                       module Conv : CONV
                       (*! sharing Whnf.IntSyn = IntSyn' !*)
                       module Abstract : ABSTRACT
                       (*! sharing Abstract.IntSyn = IntSyn' !*)
                       module Unify : UNIFY
                       (* must be trailing! *)
                       (*! sharing Unify.IntSyn = IntSyn' !*)
                       module Constraints : CONSTRAINTS
                       (*! sharing Constraints.IntSyn = IntSyn' !*)
                       module ModeTable : MODETABLE
                       module UniqueTable : MODETABLE
                       module Index : INDEX
                       (*! sharing Index.IntSyn = IntSyn' !*)
                       module Subordinate : SUBORDINATE
                       (*! sharing Subordinate.IntSyn = IntSyn' !*)
                       module WorldSyn : WORLDSYN
                       module Names : NAMES
                       (*! sharing Names.IntSyn = IntSyn' !*)
                       (*! structure Paths : PATHS !*)
                       module Print : PRINT
                       (*! sharing Print.IntSyn = IntSyn' !*)
                       module TypeCheck : TYPECHECK
                       (*! sharing TypeCheck.IntSyn = IntSyn' !*)
                       (*! structure CSManager : CS_MANAGER !*)
                       (*! sharing CSManager.IntSyn = IntSyn' !*)
                       module Timers : TIMERS
                       end) : COVER
  =
  struct
    exception Error of string ;;
    open!
      struct
        module I = IntSyn;;
        module T = Tomega;;
        module M = ModeSyn;;
        module W = WorldSyn;;
        module P = Paths;;
        module F = Print.Formatter;;
        module N = Names;;
        let rec weaken =
          function 
                   | (null_, a) -> I.id
                   | (I.Decl (g'_, (I.Dec (name, v_) as d_)), a)
                       -> let w' = weaken (g'_, a) in begin
                            if Subordinate.belowEq (I.targetFam v_, a) then
                            I.dot1 w' else I.comp (w', I.shift) end;;
        let rec createEVar (g_, v_) =
          let w = weaken (g_, I.targetFam v_)
            in let iw = Whnf.invert w
                 in let g'_ = Whnf.strengthen (iw, g_)
                      in let x'_ = Whnf.newLoweredEVar (g'_, (v_, iw))
                           in let x_ = (I.EClo (x'_, w)) in x_;;
        type coverInst_ = | Match of coverInst_ 
                          | Skip of coverInst_ 
                          | Cnil ;;
        let rec inCoverInst =
          function 
                   | mnil_ -> Cnil
                   | M.Mapp (M.Marg (plus_, x), ms')
                       -> (Match (inCoverInst ms'))
                   | M.Mapp (M.Marg (minus_, x), ms')
                       -> (Skip (inCoverInst ms'))
                   | M.Mapp (M.Marg (star_, x), ms')
                       -> (Skip (inCoverInst ms'));;
        let rec outCoverInst =
          function 
                   | mnil_ -> Cnil
                   | M.Mapp (M.Marg (plus_, x), ms')
                       -> (Skip (outCoverInst ms'))
                   | M.Mapp (M.Marg (minus_, x), ms')
                       -> (Match (outCoverInst ms'));;
        type caseLabel = | Top 
                         | Child of caseLabel * int ;;
        let rec labToString =
          function 
                   | Top -> "^"
                   | Child (lab, n)
                       -> ((labToString lab) ^ ".") ^ (Int.toString n);;
        let rec chatter chlev f = begin
          if (! Global.chatter) >= chlev then print (f ()) else () end;;
        let rec pluralize = function 
                                     | (1, s) -> s
                                     | (n, s) -> s ^ "s";;
        let rec abbrevCSpine (s_, ci) = s_;;
        let rec abbrevCGoal =
          function 
                   | (g_, v_, 0, ci) -> (g_, abbrevCGoal' (g_, v_, ci))
                   | (g_, I.Pi ((d_, p_), v_), p, ci)
                       -> let d'_ = N.decEName (g_, d_)
                            in abbrevCGoal
                               ((I.Decl (g_, d'_)), v_, p - 1, ci)
        and abbrevCGoal' =
          function 
                   | (g_, I.Pi ((d_, p_), v_), ci)
                       -> let d'_ = N.decUName (g_, d_)
                            in (I.Pi
                                ((d'_, p_),
                                 abbrevCGoal' ((I.Decl (g_, d'_)), v_, ci)))
                   | (g_, I.Root (a, s_), ci)
                       -> (I.Root (a, abbrevCSpine (s_, ci)));;
        let rec formatCGoal (v_, p, ci) =
          let _ = N.varReset I.null_
            in let (g_, v'_) = abbrevCGoal (I.null_, v_, p, ci)
                 in (F.HVbox
                     [Print.formatCtx (I.null_, g_); F.break_;
                      (F.String "|-"); F.space_; Print.formatExp (g_, v'_)]);;
        let rec formatCGoals =
          function 
                   | (((v_, p) :: []), ci) -> [formatCGoal (v_, p, ci)]
                   | (((v_, p) :: vs_), ci)
                       -> (formatCGoal (v_, p, ci) :: (F.String ",")
                           :: F.break_ :: formatCGoals (vs_, ci));;
        let rec missingToString (vs_, ci) =
          F.makestring_fmt
          ((F.Hbox
            [(F.Vbox0 (0, 1, formatCGoals (vs_, ci))); (F.String ".")]));;
        let rec showSplitVar (v_, p, k, ci) =
          let _ = N.varReset I.null_
            in let (g_, v'_) = abbrevCGoal (I.null_, v_, p, ci)
                 in let I.Dec (Some x, _) = I.ctxLookup (g_, k)
                      in (("Split " ^ x) ^ " in ") ^
                           (Print.expToString (g_, v'_));;
        let rec showPendingGoal (v_, p, ci, lab) =
          F.makestring_fmt
          ((F.Hbox
            [(F.String (labToString lab)); F.space_; (F.String "?- ");
             formatCGoal (v_, p, ci); (F.String ".")]));;
        let rec buildSpine =
          function 
                   | 0 -> I.nil_
                   | n
                       -> (I.App
                           ((I.Root ((I.BVar n), I.nil_)),
                            buildSpine (n - 1)));;
        let rec initCGoal' =
          function 
                   | (a, k, g_, I.Pi ((d_, p_), v_))
                       -> let d'_ = N.decEName (g_, d_)
                            in let (v'_, p) =
                                 initCGoal'
                                 (a, k + 1, (I.Decl (g_, d'_)), v_)
                                 in ((I.Pi ((d'_, I.maybe_), v'_)), p)
                   | (a, k, g_, I.Uni type_)
                       -> ((I.Root (a, buildSpine k)), k);;
        let rec initCGoal a =
          initCGoal' ((I.Const a), 0, I.null_, I.constType a);;
        type coverClauses_ = | Input of I.exp_ list 
                             | Output of I.exp_ * int ;;
        type equation_ = | Eqn of I.dctx * I.eclo * I.eclo ;;
        let rec equationToString (Eqn (g_, us1_, us2_)) =
          let g'_ = Names.ctxLUName g_
            in let fmt =
                 (F.HVbox
                  [Print.formatCtx (I.null_, g'_); F.break_; (F.String "|-");
                   F.space_; Print.formatExp (g'_, (I.EClo us1_)); F.break_;
                   (F.String "="); F.space_;
                   Print.formatExp (g'_, (I.EClo us2_))])
                 in F.makestring_fmt fmt;;
        let rec eqnsToString =
          function 
                   | [] -> ".\n"
                   | (eqn :: eqns)
                       -> ((equationToString eqn) ^ ",\n") ^
                            (eqnsToString eqns);;
        type candidates_ =
          | Eqns of equation_ list 
          | Cands of int list 
          | Fail ;;
        let rec candsToString =
          function 
                   | Fail -> "Fail"
                   | Cands ks
                       -> "Cands [" ^
                            (List.foldl
                             (function 
                                       | (k, str)
                                           -> ((Int.toString k) ^ ",") ^ str)
                             "]"
                             ks)
                   | Eqns eqns -> ("Eqns [\n" ^ (eqnsToString eqns)) ^ "]";;
        let rec fail msg =
          begin
            chatter 7 (function 
                                | () -> msg ^ "\n");Fail
            end;;
        let rec failAdd =
          function 
                   | (k, Eqns _) -> (Cands [k])
                   | (k, Cands ks) -> (Cands ((k :: ks)))
                   | (k, Fail) -> Fail;;
        let rec addEqn =
          function 
                   | (e, Eqns es) -> (Eqns ((e :: es)))
                   | (e, (Cands ks as cands)) -> cands
                   | (e, Fail) -> Fail;;
        let rec unifiable (g_, us1_, us2_) = Unify.unifiable (g_, us1_, us2_);;
        let rec matchEqns =
          function 
                   | [] -> true
                   | (Eqn (g_, us1_, ((u2_, s2) as us2_)) :: es)
                       -> (begin
                           match Whnf.makePatSub s2
                           with 
                                | None -> unifiable (g_, us1_, us2_)
                                | Some s2'
                                    -> unifiable (g_, us1_, (u2_, s2'))
                           end) && (matchEqns es);;
        let rec resolveCands =
          function 
                   | Eqns es -> begin
                       if matchEqns (List.rev es) then (Eqns []) else Fail
                       end
                   | Cands ks -> (Cands ks)
                   | Fail -> Fail;;
        let rec collectConstraints =
          function 
                   | [] -> []
                   | (I.EVar (_, _, _, { contents = []}) :: xs_)
                       -> collectConstraints xs_
                   | (I.EVar (_, _, _, { contents = constrs}) :: xs_)
                       -> constrs @ (collectConstraints xs_);;
        let rec checkConstraints =
          function 
                   | (g_, qs_, Cands ks) -> (Cands ks)
                   | (g_, qs_, Fail) -> Fail
                   | (g_, qs_, Eqns _)
                       -> let xs_ = Abstract.collectEVars (g_, qs_, [])
                            in let constrs = collectConstraints xs_
                                 in begin
                                    match constrs
                                    with 
                                         | [] -> (Eqns [])
                                         | _ -> Fail
                                    end;;
        type candList_ = | Covered 
                         | CandList of candidates_ list ;;
        let rec addKs =
          function 
                   | ((Cands ks as ccs), CandList klist)
                       -> (CandList ((ccs :: klist)))
                   | ((Eqns [] as ces), CandList klist) -> Covered
                   | ((Fail as cfl), CandList klist)
                       -> (CandList ((cfl :: klist)));;
        let rec matchExp (g_, d, us1_, us2_, cands) =
          matchExpW (g_, d, Whnf.whnf us1_, Whnf.whnf us2_, cands)
        and matchExpW =
          function 
                   | (g_, d, ((I.Root (h1_, s1_), s1) as us1_),
                      ((I.Root (h2_, s2_), s2) as us2_), cands)
                       -> begin
                          match (h1_, h2_)
                          with 
                               | (I.BVar k1, I.BVar k2) -> begin
                                   if k1 = k2 then
                                   matchSpine
                                   (g_, d, (s1_, s1), (s2_, s2), cands) else
                                   begin
                                   if k1 > d then failAdd (k1 - d, cands)
                                   else
                                   fail "local variable / variable clash" end
                                   end
                               | (I.Const c1, I.Const c2) -> begin
                                   if c1 = c2 then
                                   matchSpine
                                   (g_, d, (s1_, s1), (s2_, s2), cands) else
                                   fail "constant / constant clash" end
                               | (I.Def d1, I.Def d2) -> begin
                                   if d1 = d2 then
                                   matchSpine
                                   (g_, d, (s1_, s1), (s2_, s2), cands) else
                                   matchExpW
                                   (g_, d, Whnf.expandDef us1_,
                                    Whnf.expandDef us2_, cands)
                                   end
                               | (I.Def d1, _)
                                   -> matchExpW
                                      (g_, d, Whnf.expandDef us1_, us2_,
                                       cands)
                               | (_, I.Def d2)
                                   -> matchExpW
                                      (g_, d, us1_, Whnf.expandDef us2_,
                                       cands)
                               | (I.BVar k1, I.Const _) -> begin
                                   if k1 > d then failAdd (k1 - d, cands)
                                   else
                                   fail "local variable / constant clash" end
                               | (I.Const _, I.BVar _)
                                   -> fail "constant / local variable clash"
                               | (I.Proj (I.Bidx k1, i1), I.Proj
                                  (I.Bidx k2, i2)) -> begin
                                   if (k1 = k2) && (i1 = i2) then
                                   matchSpine
                                   (g_, d, (s1_, s1), (s2_, s2), cands) else
                                   fail "block index / block index clash" end
                               | (I.Proj (I.Bidx k1, i1), I.Proj
                                  (I.LVar (r2, I.Shift k2, (l2, t2)), i2))
                                   -> let I.BDec (bOpt, (l1, t1)) =
                                        I.ctxDec (g_, k1) in begin
                                        if (l1 <> l2) || (i1 <> i2) then
                                        fail
                                        "block index / block variable clash"
                                        else
                                        let cands2 =
                                          matchSub
                                          (g_, d, t1,
                                           I.comp (t2, (I.Shift k2)), cands)
                                          in let _ =
                                               Unify.instantiateLVar
                                               (r2, (I.Bidx (k1 - k2)))
                                               in matchSpine
                                                  (g_, d, (s1_, s1),
                                                   (s2_, s2), cands2)
                                        end
                               | (I.BVar k1, I.Proj _) -> begin
                                   if k1 > d then failAdd (k1 - d, cands)
                                   else
                                   fail
                                   "local variable / block projection clash"
                                   end
                               | (I.Const _, I.Proj _)
                                   -> fail
                                      "constant / block projection clash"
                               | (I.Proj _, I.Const _)
                                   -> fail
                                      "block projection / constant clash"
                               | (I.Proj _, I.BVar _)
                                   -> fail
                                      "block projection / local variable clash"
                          end
                   | (g_, d, (I.Lam (d1_, u1_), s1), (I.Lam (d2_, u2_), s2),
                      cands)
                       -> matchExp
                          ((I.Decl (g_, I.decSub (d1_, s1))), d + 1,
                           (u1_, I.dot1 s1), (u2_, I.dot1 s2), cands)
                   | (g_, d, (I.Lam (d1_, u1_), s1), (u2_, s2), cands)
                       -> matchExp
                          ((I.Decl (g_, I.decSub (d1_, s1))), d + 1,
                           (u1_, I.dot1 s1),
                           ((I.Redex
                             ((I.EClo (u2_, I.shift)),
                              (I.App ((I.Root ((I.BVar 1), I.nil_)), I.nil_)))),
                            I.dot1 s2),
                           cands)
                   | (g_, d, (u1_, s1), (I.Lam (d2_, u2_), s2), cands)
                       -> matchExp
                          ((I.Decl (g_, I.decSub (d2_, s2))), d + 1,
                           ((I.Redex
                             ((I.EClo (u1_, I.shift)),
                              (I.App ((I.Root ((I.BVar 1), I.nil_)), I.nil_)))),
                            I.dot1 s1),
                           (u2_, I.dot1 s2), cands)
                   | (g_, d, us1_, ((I.EVar _, s2) as us2_), cands)
                       -> addEqn ((Eqn (g_, us1_, us2_)), cands)
        and matchSpine =
          function 
                   | (g_, d, (nil_, _), (nil_, _), cands) -> cands
                   | (g_, d, (I.SClo (s1_, s1'), s1), ss2_, cands)
                       -> matchSpine
                          (g_, d, (s1_, I.comp (s1', s1)), ss2_, cands)
                   | (g_, d, ss1_, (I.SClo (s2_, s2'), s2), cands)
                       -> matchSpine
                          (g_, d, ss1_, (s2_, I.comp (s2', s2)), cands)
                   | (g_, d, (I.App (u1_, s1_), s1), (I.App (u2_, s2_), s2),
                      cands)
                       -> let cands' =
                            matchExp (g_, d, (u1_, s1), (u2_, s2), cands)
                            in matchSpine
                               (g_, d, (s1_, s1), (s2_, s2), cands')
        and matchDec
          (g_, d, (I.Dec (_, v1_), s1), (I.Dec (_, v2_), s2), cands) =
          matchExp (g_, d, (v1_, s1), (v2_, s2), cands)
        and matchSub =
          function 
                   | (g_, d, I.Shift n1, I.Shift n2, cands) -> cands
                   | (g_, d, I.Shift n, (I.Dot _ as s2), cands)
                       -> matchSub
                          (g_, d,
                           (I.Dot ((I.Idx (n + 1)), (I.Shift (n + 1)))), s2,
                           cands)
                   | (g_, d, (I.Dot _ as s1), I.Shift m, cands)
                       -> matchSub
                          (g_, d, s1,
                           (I.Dot ((I.Idx (m + 1)), (I.Shift (m + 1)))),
                           cands)
                   | (g_, d, I.Dot (ft1_, s1), I.Dot (ft2_, s2), cands)
                       -> let cands1 =
                            begin
                            match (ft1_, ft2_)
                            with 
                                 | (I.Idx n1, I.Idx n2) -> begin
                                     if n1 = n2 then cands else begin
                                     if n1 > d then failAdd (n1 - d, cands)
                                     else
                                     fail
                                     "local variable / local variable clash in block instance"
                                     end end
                                 | (I.Exp u1_, I.Exp u2_)
                                     -> matchExp
                                        (g_, d, (u1_, I.id), (u2_, I.id),
                                         cands)
                                 | (I.Exp u1_, I.Idx n2)
                                     -> matchExp
                                        (g_, d, (u1_, I.id),
                                         ((I.Root ((I.BVar n2), I.nil_)),
                                          I.id),
                                         cands)
                                 | (I.Idx n1, I.Exp u2_)
                                     -> matchExp
                                        (g_, d,
                                         ((I.Root ((I.BVar n1), I.nil_)),
                                          I.id),
                                         (u2_, I.id), cands)
                            end in matchSub (g_, d, s1, s2, cands1);;
        let rec matchTop (g_, d, us1_, us2_, ci, cands) =
          matchTopW (g_, d, Whnf.whnf us1_, Whnf.whnf us2_, ci, cands)
        and matchTopW =
          function 
                   | (g_, d, (I.Root (I.Const c1, s1_), s1),
                      (I.Root (I.Const c2, s2_), s2), ci, cands) -> begin
                       if c1 = c2 then
                       matchTopSpine (g_, d, (s1_, s1), (s2_, s2), ci, cands)
                       else fail "type family clash" end
                   | (g_, d, (I.Pi ((d1_, _), v1_), s1),
                      (I.Pi ((d2_, _), v2_), s2), ci, cands)
                       -> matchTopW
                          ((I.Decl (g_, d1_)), d + 1, (v1_, I.dot1 s1),
                           (v2_, I.dot1 s2), ci, cands)
        and matchTopSpine =
          function 
                   | (g_, d, (nil_, _), (nil_, _), Cnil, cands) -> cands
                   | (g_, d, (I.SClo (s1_, s1'), s1), ss2_, ci, cands)
                       -> matchTopSpine
                          (g_, d, (s1_, I.comp (s1', s1)), ss2_, ci, cands)
                   | (g_, d, ss1_, (I.SClo (s2_, s2'), s2), ci, cands)
                       -> matchTopSpine
                          (g_, d, ss1_, (s2_, I.comp (s2', s2)), ci, cands)
                   | (g_, d, (I.App (u1_, s1_), s1), (I.App (u2_, s2_), s2),
                      Match ci', cands)
                       -> let cands' =
                            matchExp (g_, d, (u1_, s1), (u2_, s2), cands)
                            in matchTopSpine
                               (g_, d, (s1_, s1), (s2_, s2), ci', cands')
                   | (g_, d, (I.App (u1_, s1_), s1), (I.App (u2_, s2_), s2),
                      Skip ci', cands)
                       -> matchTopSpine
                          (g_, d, (s1_, s1), (s2_, s2), ci', cands);;
        let rec matchClause =
          function 
                   | (g_, ps', ((I.Root (_, _), s) as qs), ci)
                       -> checkConstraints
                          (g_, qs,
                           resolveCands
                           (matchTop (g_, 0, ps', qs, ci, (Eqns []))))
                   | (g_, ps', (I.Pi ((I.Dec (_, v1_), _), v2_), s), ci)
                       -> let x1_ = Whnf.newLoweredEVar (g_, (v1_, s))
                            in matchClause
                               (g_, ps', (v2_, (I.Dot ((I.Exp x1_), s))), ci);;
        let rec matchSig =
          function 
                   | (g_, ps', [], ci, klist) -> klist
                   | (g_, ps', (v_ :: ccs'), ci, klist)
                       -> let cands =
                            CSManager.trail
                            (function 
                                      | ()
                                          -> matchClause
                                             (g_, ps', (v_, I.id), ci))
                            in matchSig'
                               (g_, ps', ccs', ci, addKs (cands, klist))
        and matchSig' =
          function 
                   | (g_, ps', ccs, ci, Covered) -> Covered
                   | (g_, ps', ccs, ci, CandList klist)
                       -> matchSig (g_, ps', ccs, ci, (CandList klist));;
        let rec matchBlocks =
          function 
                   | (g_, s', [], v_, k, i, ci, klist) -> klist
                   | (g_, s', (I.Dec (_, v'_) :: piDecs), v_, k, i, ci,
                      klist)
                       -> let cands =
                            CSManager.trail
                            (function 
                                      | ()
                                          -> matchClause
                                             (g_, (v_, I.id), (v'_, s'), ci))
                            in let s'' =
                                 (I.Dot
                                  ((I.Exp
                                    ((I.Root
                                      ((I.Proj ((I.Bidx k), i)), I.nil_)))),
                                   s'))
                                 in matchBlocks'
                                    (g_, s'', piDecs, v_, k, i + 1, ci,
                                     addKs (cands, klist))
        and matchBlocks' =
          function 
                   | (g_, s', piDecs, v_, k, i, ci, Covered) -> Covered
                   | (g_, s', piDecs, v_, k, i, ci, klist)
                       -> matchBlocks (g_, s', piDecs, v_, k, i, ci, klist);;
        let rec matchCtx =
          function 
                   | (g_, s', null_, v_, k, ci, klist) -> klist
                   | (g_, s', I.Decl (g''_, I.Dec (_, v'_)), v_, k, ci,
                      klist)
                       -> let s'' = I.comp (I.shift, s')
                            in let cands =
                                 CSManager.trail
                                 (function 
                                           | ()
                                               -> matchClause
                                                  (g_, (v_, I.id),
                                                   (v'_, s''), ci))
                                 in matchCtx'
                                    (g_, s'', g''_, v_, k + 1, ci,
                                     addKs (cands, klist))
                   | (g_, s', I.Decl (g''_, I.BDec (_, (cid, s))), v_, k, ci,
                      klist)
                       -> let (gsome_, piDecs) = I.constBlock cid
                            in let s'' = I.comp (I.shift, s')
                                 in let klist' =
                                      matchBlocks
                                      (g_, I.comp (s, s''), piDecs, v_, k, 1,
                                       ci, klist)
                                      in matchCtx'
                                         (g_, s'', g''_, v_, k + 1, ci,
                                          klist')
        and matchCtx' =
          function 
                   | (g_, s', g'_, v_, k, ci, Covered) -> Covered
                   | (g_, s', g'_, v_, k, ci, CandList klist)
                       -> matchCtx (g_, s', g'_, v_, k, ci, (CandList klist));;
        let rec matchOut =
          function 
                   | (g_, v_, ci, (v'_, s'), 0)
                       -> let cands =
                            matchTop
                            (g_, 0, (v_, I.id), (v'_, s'), ci, (Eqns []))
                            in let cands' = resolveCands cands
                                 in let cands'' =
                                      checkConstraints
                                      (g_, (v'_, s'), cands')
                                      in addKs (cands'', (CandList []))
                   | (g_, v_, ci,
                      ((I.Pi ((I.Dec (_, v1'_), _), v2'_) as v'_), s'), p)
                       -> let x1_ = Whnf.newLoweredEVar (g_, (v1'_, s'))
                            in matchOut
                               (g_, v_, ci,
                                (v2'_, (I.Dot ((I.Exp x1_), s'))), p - 1);;
        let rec match_ =
          function 
                   | (g_, (I.Root (I.Const a, s_) as v_), 0, ci, Input ccs)
                       -> matchCtx'
                          (g_, I.id, g_, v_, 1, ci,
                           matchSig (g_, (v_, I.id), ccs, ci, (CandList [])))
                   | (g_, v_, 0, ci, Output (v'_, q))
                       -> matchOut
                          (g_, v_, ci, (v'_, (I.Shift (I.ctxLength g_))), q)
                   | (g_, I.Pi ((d_, _), v'_), p, ci, ccs)
                       -> match_ ((I.Decl (g_, d_)), v'_, p - 1, ci, ccs);;
        let rec insert =
          function 
                   | (k, []) -> [(k, 1)]
                   | (k, (((k', n') :: ksn') as ksn))
                       -> begin
                          match Int.compare (k, k')
                          with 
                               | LESS -> ((k, 1) :: ksn)
                               | EQUAL -> ((k', n' + 1) :: ksn')
                               | GREATER -> ((k', n') :: insert (k, ksn'))
                          end;;
        let rec join =
          function 
                   | ([], ksn) -> ksn
                   | ((k :: ks), ksn) -> join (ks, insert (k, ksn));;
        let rec selectCand =
          function 
                   | Covered -> None
                   | CandList klist -> selectCand' (klist, [])
        and selectCand' =
          function 
                   | ([], ksn) -> (Some ksn)
                   | ((Fail :: klist), ksn) -> selectCand' (klist, ksn)
                   | ((Cands [] :: klist), ksn) -> selectCand' (klist, ksn)
                   | ((Cands ks :: klist), ksn)
                       -> selectCand' (klist, join (ks, ksn));;
        let rec instEVars (vs_, p, xsRev_) =
          instEVarsW (Whnf.whnf vs_, p, xsRev_)
        and instEVarsW =
          function 
                   | (vs_, 0, xsRev_) -> (vs_, xsRev_)
                   | ((I.Pi ((I.Dec (xOpt, v1_), _), v2_), s), p, xsRev_)
                       -> let x1_ = Whnf.newLoweredEVar (I.null_, (v1_, s))
                            in instEVars
                               ((v2_, (I.Dot ((I.Exp x1_), s))), p - 1,
                                ((Some x1_) :: xsRev_))
                   | ((I.Pi ((I.BDec (_, (l, t)), _), v2_), s), p, xsRev_)
                       -> let l1_ =
                            I.newLVar ((I.Shift 0), (l, I.comp (t, s)))
                            in instEVars
                               ((v2_, (I.Dot ((I.Block l1_), s))), p - 1,
                                (None :: xsRev_));;
        open! struct
                let caseList : (I.exp_ * int) list ref = ref [];;
                end;;
        let rec resetCases () = caseList := [];;
        let rec addCase (v_, p) = caseList := (((v_, p) :: ! caseList));;
        let rec getCases () = ! caseList;;
        let rec createEVarSpine (g_, vs_) =
          createEVarSpineW (g_, Whnf.whnf vs_)
        and createEVarSpineW =
          function 
                   | (g_, ((I.Root _, s) as vs_)) -> (I.nil_, vs_)
                   | (g_, (I.Pi (((I.Dec (_, v1_) as d_), _), v2_), s))
                       -> let x_ = createEVar (g_, (I.EClo (v1_, s)))
                            in let (s_, vs_) =
                                 createEVarSpine
                                 (g_, (v2_, (I.Dot ((I.Exp x_), s))))
                                 in ((I.App (x_, s_)), vs_);;
        let rec createAtomConst (g_, (I.Const cid as h_)) =
          let v_ = I.constType cid
            in let (s_, vs_) = createEVarSpine (g_, (v_, I.id))
                 in ((I.Root (h_, s_)), vs_);;
        let rec createAtomBVar (g_, k) =
          let I.Dec (_, v_) = I.ctxDec (g_, k)
            in let (s_, vs_) = createEVarSpine (g_, (v_, I.id))
                 in ((I.Root ((I.BVar k), s_)), vs_);;
        let rec createAtomProj (g_, h_, (v_, s)) =
          let (s_, vs'_) = createEVarSpine (g_, (v_, s))
            in ((I.Root (h_, s_)), vs'_);;
        let rec constCases =
          function 
                   | (g_, vs_, [], sc) -> ()
                   | (g_, vs_, (I.Const c :: sgn'), sc)
                       -> let (u_, vs'_) = createAtomConst (g_, (I.Const c))
                            in let _ =
                                 CSManager.trail
                                 (function 
                                           | () -> begin
                                               if
                                               Unify.unifiable
                                               (g_, vs_, vs'_) then sc u_
                                               else () end)
                                 in constCases (g_, vs_, sgn', sc);;
        let rec paramCases =
          function 
                   | (g_, vs_, 0, sc) -> ()
                   | (g_, vs_, k, sc)
                       -> let (u_, vs'_) = createAtomBVar (g_, k)
                            in let _ =
                                 CSManager.trail
                                 (function 
                                           | () -> begin
                                               if
                                               Unify.unifiable
                                               (g_, vs_, vs'_) then sc u_
                                               else () end)
                                 in paramCases (g_, vs_, k - 1, sc);;
        let rec createEVarSub =
          function 
                   | null_ -> I.id
                   | I.Decl (g'_, (I.Dec (_, v_) as d_))
                       -> let s = createEVarSub g'_
                            in let x_ =
                                 Whnf.newLoweredEVar (I.null_, (v_, s))
                                 in (I.Dot ((I.Exp x_), s));;
        let rec blockName cid = I.conDecName (I.sgnLookup cid);;
        let rec blockCases (g_, vs_, cid, (gsome_, piDecs), sc) =
          let t = createEVarSub gsome_
            in let sk = (I.Shift (I.ctxLength g_))
                 in let t' = I.comp (t, sk)
                      in let lvar = I.newLVar (sk, (cid, t))
                           in blockCases'
                              (g_, vs_, (lvar, 1), (t', piDecs), sc)
        and blockCases' =
          function 
                   | (g_, vs_, (lvar, i), (t, []), sc) -> ()
                   | (g_, vs_, (lvar, i), (t, (I.Dec (_, v'_) :: piDecs)),
                      sc)
                       -> let (u_, vs'_) =
                            createAtomProj (g_, (I.Proj (lvar, i)), (v'_, t))
                            in let _ =
                                 CSManager.trail
                                 (function 
                                           | () -> begin
                                               if
                                               Unify.unifiable
                                               (g_, vs_, vs'_) then sc u_
                                               else () end)
                                 in let t' =
                                      (I.Dot
                                       ((I.Exp
                                         ((I.Root
                                           ((I.Proj (lvar, i)), I.nil_)))),
                                        t))
                                      in blockCases'
                                         (g_, vs_, (lvar, i + 1),
                                          (t', piDecs), sc);;
        let rec worldCases =
          function 
                   | (g_, vs_, T.Worlds [], sc) -> ()
                   | (g_, vs_, T.Worlds ((cid :: cids)), sc)
                       -> begin
                            blockCases (g_, vs_, cid, I.constBlock cid, sc);
                            worldCases (g_, vs_, (T.Worlds cids), sc)
                            end;;
        let rec lowerSplitW =
          function 
                   | ((I.EVar (_, g_, v_, _) as x_), w_, sc)
                       -> let sc' =
                            function 
                                     | u_ -> begin
                                         if
                                         Unify.unifiable
                                         (g_, (x_, I.id), (u_, I.id)) then
                                         sc () else () end
                            in let _ =
                                 paramCases
                                 (g_, (v_, I.id), I.ctxLength g_, sc')
                                 in let _ =
                                      worldCases (g_, (v_, I.id), w_, sc')
                                      in let _ =
                                           constCases
                                           (g_, (v_, I.id),
                                            Index.lookup (I.targetFam v_),
                                            sc')
                                           in ()
                   | (I.Lam (d_, u_), w_, sc) -> lowerSplitW (u_, w_, sc);;
        let rec splitEVar (x_, w_, sc) = lowerSplitW (x_, w_, sc);;
        let rec abstract (v_, s) =
          let (i, v'_) = Abstract.abstractDecImp ((I.EClo (v_, s)))
            in let _ = begin
                 if ! Global.doubleCheck then
                 TypeCheck.typeCheck (I.null_, (v'_, (I.Uni I.type_))) else
                 () end in (v'_, i);;
        let rec splitVar (v_, p, k, (w_, ci)) =
          try let _ =
                chatter
                6
                (function 
                          | () -> (showSplitVar (v_, p, k, ci)) ^ "\n")
                in let ((v1_, s), xsRev_) = instEVars ((v_, I.id), p, [])
                     in let Some x_ = List.nth (xsRev_, k - 1)
                          in let _ = resetCases ()
                               in let _ =
                                    splitEVar
                                    (x_, w_,
                                     function 
                                              | ()
                                                  -> addCase
                                                     (abstract (v1_, s)))
                                    in (Some (getCases ()))
          with 
               | Constraints.Error constrs
                   -> begin
                        chatter
                        7
                        (function 
                                  | ()
                                      -> ("Inactive split:\n" ^
                                            (Print.cnstrsToString constrs))
                                           ^ "\n");
                        None
                        end;;
        let rec occursInExp =
          function 
                   | (k, I.Uni _) -> false
                   | (k, I.Pi (dp_, v_))
                       -> (occursInDecP (k, dp_)) ||
                            (occursInExp (k + 1, v_))
                   | (k, I.Root (h_, s_))
                       -> (occursInHead (k, h_)) || (occursInSpine (k, s_))
                   | (k, I.Lam (d_, v_))
                       -> (occursInDec (k, d_)) || (occursInExp (k + 1, v_))
                   | (k, I.FgnExp (cs, ops)) -> false
        and occursInHead =
          function 
                   | (k, I.BVar k') -> k = k'
                   | (k, _) -> false
        and occursInSpine =
          function 
                   | (_, nil_) -> false
                   | (k, I.App (u_, s_))
                       -> (occursInExp (k, u_)) || (occursInSpine (k, s_))
        and occursInDec (k, I.Dec (_, v_)) = occursInExp (k, v_)
        and occursInDecP (k, (d_, _)) = occursInDec (k, d_);;
        let rec occursInMatchPos =
          function 
                   | (k, I.Pi (dp_, v_), ci)
                       -> occursInMatchPos (k + 1, v_, ci)
                   | (k, I.Root (h_, s_), ci)
                       -> occursInMatchPosSpine (k, s_, ci)
        and occursInMatchPosSpine =
          function 
                   | (k, nil_, Cnil) -> false
                   | (k, I.App (u_, s_), Match ci)
                       -> (occursInExp (k, u_)) ||
                            (occursInMatchPosSpine (k, s_, ci))
                   | (k, I.App (u_, s_), Skip ci)
                       -> occursInMatchPosSpine (k, s_, ci);;
        let rec instEVarsSkip (vs_, p, xsRev_, ci) =
          instEVarsSkipW_ (Whnf.whnf vs_, p, xsRev_, ci)
        and instEVarsSkipW_ =
          function 
                   | (vs_, 0, xsRev_, ci) -> (vs_, xsRev_)
                   | ((I.Pi ((I.Dec (xOpt, v1_), _), v2_), s), p, xsRev_, ci)
                       -> let x1_ = Whnf.newLoweredEVar (I.null_, (v1_, s))
                            in let eVarOpt_ = begin
                                 if occursInMatchPos (1, v2_, ci) then
                                 (Some x1_) else None end
                                 in instEVarsSkip
                                    ((v2_, (I.Dot ((I.Exp x1_), s))), 
                                     p - 1, (eVarOpt_ :: xsRev_), ci)
                   | ((I.Pi ((I.BDec (_, (l, t)), _), v2_), s), p, xsRev_,
                      ci)
                       -> let l1_ =
                            I.newLVar ((I.Shift 0), (l, I.comp (t, s)))
                            in instEVarsSkip
                               ((v2_, (I.Dot ((I.Block l1_), s))), p - 1,
                                (None :: xsRev_), ci);;
        let rec targetBelowEq =
          function 
                   | (a, I.EVar
                      ({ contents = None}, gy_, vy_, { contents = []}))
                       -> Subordinate.belowEq (a, I.targetFam vy_)
                   | (a, I.EVar
                      ({ contents = None}, gy_, vy_, { contents = (_ :: _)}))
                       -> true;;
        let rec recursive =
          function 
                   | (I.EVar ({ contents = Some u_}, gx_, vx_, _) as x_)
                       -> let a = I.targetFam vx_
                            in let ys_ =
                                 Abstract.collectEVars (gx_, (x_, I.id), [])
                                 in let recp =
                                      List.exists
                                      (function 
                                                | y_ -> targetBelowEq (a, y_))
                                      ys_ in recp
                   | I.Lam (d_, u_) -> recursive u_;;
        open! struct
                let counter = ref 0;;
                end;;
        let rec resetCount () = counter := 0;;
        let rec incCount () = counter := ((! counter) + 1);;
        let rec getCount () = ! counter;;
        exception NotFinitary ;;
        let rec finitary1 (x_, k, w_, f, cands) =
          begin
            resetCount ();
            begin
              chatter
              7
              (function 
                        | ()
                            -> (("Trying " ^
                                   (Print.expToString (I.null_, x_)))
                                  ^ " : ")
                                 ^ ".\n");
              try begin
                    splitEVar
                    (x_, w_,
                     function 
                              | ()
                                  -> begin
                                       f ();begin
                                       if recursive x_ then raise NotFinitary
                                       else incCount () end
                                       end);
                    begin
                      chatter
                      7
                      (function 
                                | ()
                                    -> ("Finitary with " ^
                                          (Int.toString (getCount ())))
                                         ^ " candidates.\n");
                      ((k, getCount ()) :: cands)
                      end
                    
                    end
              with 
                   | NotFinitary
                       -> begin
                            chatter 7 (function 
                                                | () -> "Not finitary.\n");
                            cands
                            end
                   | Constraints.Error constrs
                       -> begin
                            chatter
                            7
                            (function 
                                      | () -> "Inactive finitary split.\n");
                            cands
                            end
              
              end
            
            end;;
        let rec finitarySplits =
          function 
                   | ([], k, w_, f, cands) -> cands
                   | ((None :: xs_), k, w_, f, cands)
                       -> finitarySplits (xs_, k + 1, w_, f, cands)
                   | ((Some x_ :: xs_), k, w_, f, cands)
                       -> finitarySplits
                          (xs_, k + 1, w_, f,
                           CSManager.trail
                           (function 
                                     | () -> finitary1 (x_, k, w_, f, cands)));;
        let rec finitary (v_, p, w_, ci) =
          let _ = begin
            if ! Global.doubleCheck then
            TypeCheck.typeCheck (I.null_, (v_, (I.Uni I.type_))) else () end
            in let ((v1_, s), xsRev_) = instEVarsSkip ((v_, I.id), p, [], ci)
                 in finitarySplits
                    (xsRev_, 1, w_, function 
                                             | () -> abstract (v1_, s), []);;
        let rec eqExp (us_, us'_) = Conv.conv (us_, us'_);;
        let rec eqInpSpine =
          function 
                   | (ms, (I.SClo (s1_, s1'), s1), ss2_)
                       -> eqInpSpine (ms, (s1_, I.comp (s1', s1)), ss2_)
                   | (ms, ss1_, (I.SClo (s2_, s2'), s2))
                       -> eqInpSpine (ms, ss1_, (s2_, I.comp (s2', s2)))
                   | (mnil_, (nil_, s), (nil_, s')) -> true
                   | (M.Mapp (M.Marg (plus_, _), ms'), (I.App (u_, s_), s),
                      (I.App (u'_, s'_), s'))
                       -> (eqExp ((u_, s), (u'_, s'))) &&
                            (eqInpSpine (ms', (s_, s), (s'_, s')))
                   | (M.Mapp (_, ms'), (I.App (u_, s_), s),
                      (I.App (u'_, s'_), s'))
                       -> eqInpSpine (ms', (s_, s), (s'_, s'));;
        let rec eqInp =
          function 
                   | (null_, k, a, ss_, ms) -> []
                   | (I.Decl (g'_, I.Dec (_, I.Root (I.Const a', s'_))), k,
                      a, ss_, ms) -> begin
                       if
                       (a = a') && (eqInpSpine (ms, (s'_, (I.Shift k)), ss_))
                       then (k :: eqInp (g'_, k + 1, a, ss_, ms)) else
                       eqInp (g'_, k + 1, a, ss_, ms) end
                   | (I.Decl (g'_, I.Dec (_, I.Pi _)), k, a, ss_, ms)
                       -> eqInp (g'_, k + 1, a, ss_, ms)
                   | (I.Decl (g'_, I.NDec _), k, a, ss_, ms)
                       -> eqInp (g'_, k + 1, a, ss_, ms)
                   | (I.Decl (g'_, I.BDec (_, (b, t))), k, a, ss_, ms)
                       -> eqInp (g'_, k + 1, a, ss_, ms);;
        let rec contractionCands =
          function 
                   | (null_, k) -> []
                   | (I.Decl (g'_, I.Dec (_, I.Root (I.Const a, s_))), k)
                       -> begin
                          match UniqueTable.modeLookup a
                          with 
                               | None -> contractionCands (g'_, k + 1)
                               | Some ms
                                   -> begin
                                      match eqInp
                                            (g'_, k + 1, a,
                                             (s_, (I.Shift k)), ms)
                                      with 
                                           | []
                                               -> contractionCands
                                                  (g'_, k + 1)
                                           | ns
                                               -> ((k :: ns)
                                                   :: contractionCands
                                                      (g'_, k + 1))
                                      end
                          end
                   | (I.Decl (g'_, I.Dec (_, I.Pi _)), k)
                       -> contractionCands (g'_, k + 1)
                   | (I.Decl (g'_, I.NDec _), k)
                       -> contractionCands (g'_, k + 1)
                   | (I.Decl (g'_, I.BDec (_, (b, t))), k)
                       -> contractionCands (g'_, k + 1);;
        let rec isolateSplittable =
          function 
                   | (g_, v_, 0) -> (g_, v_)
                   | (g_, I.Pi ((d_, _), v'_), p)
                       -> isolateSplittable ((I.Decl (g_, d_)), v'_, p - 1);;
        let rec unifyUOutSpine =
          function 
                   | (ms, (I.SClo (s1_, s1'), s1), ss2_)
                       -> unifyUOutSpine (ms, (s1_, I.comp (s1', s1)), ss2_)
                   | (ms, ss1_, (I.SClo (s2_, s2'), s2))
                       -> unifyUOutSpine (ms, ss1_, (s2_, I.comp (s2', s2)))
                   | (mnil_, (nil_, s1), (nil_, s2)) -> true
                   | (M.Mapp (M.Marg (minus1_, _), ms'),
                      (I.App (u1_, s1_), s1), (I.App (u2_, s2_), s2))
                       -> (Unify.unifiable (I.null_, (u1_, s1), (u2_, s2)))
                            && (unifyUOutSpine (ms', (s1_, s1), (s2_, s2)))
                   | (M.Mapp (_, ms'), (I.App (u1_, s1_), s1),
                      (I.App (u2_, s2_), s2))
                       -> unifyUOutSpine (ms', (s1_, s1), (s2_, s2));;
        let rec unifyUOutType (v1_, v2_) =
          unifyUOutTypeW (Whnf.whnf (v1_, I.id), Whnf.whnf (v2_, I.id))
        and unifyUOutTypeW
          ((I.Root (I.Const a1, s1_), s1), (I.Root (I.Const a2, s2_), s2)) =
          let Some ms = UniqueTable.modeLookup a1
            in unifyUOutSpine (ms, (s1_, s1), (s2_, s2));;
        let rec unifyUOutEVars
          (Some (I.EVar (_, g1_, v1_, _)), Some (I.EVar (_, g2_, v2_, _))) =
          unifyUOutType (v1_, v2_);;
        let rec unifyUOut2 (xsRev_, k1, k2) =
          unifyUOutEVars
          (List.nth (xsRev_, k1 - 1), List.nth (xsRev_, k2 - 1));;
        let rec unifyUOut1 =
          function 
                   | (xsRev_, []) -> true
                   | (xsRev_, (k1 :: [])) -> true
                   | (xsRev_, (k1 :: (k2 :: ks)))
                       -> (unifyUOut2 (xsRev_, k1, k2)) &&
                            (unifyUOut1 (xsRev_, (k2 :: ks)));;
        let rec unifyUOut =
          function 
                   | (xsRev_, []) -> true
                   | (xsRev_, (ks :: kss))
                       -> (unifyUOut1 (xsRev_, ks)) &&
                            (unifyUOut (xsRev_, kss));;
        let rec contractAll (v_, p, ucands) =
          let ((v1_, s), xsRev_) = instEVars ((v_, I.id), p, []) in begin
            if unifyUOut (xsRev_, ucands) then (Some (abstract (v1_, s)))
            else None end;;
        let rec contract (v_, p, ci, lab) =
          let (g_, _) = isolateSplittable (I.null_, v_, p)
            in let ucands = contractionCands (g_, 1)
                 in let n = List.length ucands
                      in let _ = begin
                           if n > 0 then
                           chatter
                           6
                           (function 
                                     | ()
                                         -> ((("Found " ^ (Int.toString n)) ^
                                                " contraction ")
                                               ^ (pluralize (n, "candidate")))
                                              ^ "\n")
                           else () end
                           in let vpOpt'_ = begin
                                if n > 0 then
                                try contractAll (v_, p, ucands)
                                with 
                                     | Constraints.Error _
                                         -> begin
                                              chatter
                                              6
                                              (function 
                                                        | ()
                                                            -> "Contraction failed due to constraints\n");
                                              (Some (v_, p))
                                              end
                                else (Some (v_, p)) end
                                in let _ =
                                     begin
                                     match vpOpt'_
                                     with 
                                          | None
                                              -> chatter
                                                 6
                                                 (function 
                                                           | ()
                                                               -> "Case impossible: conflicting unique outputs\n")
                                          | Some (v'_, p')
                                              -> chatter
                                                 6
                                                 (function 
                                                           | ()
                                                               -> (showPendingGoal
                                                                   (v'_, p',
                                                                    ci, lab))
                                                                    ^ "\n")
                                     end in vpOpt'_;;
        let rec findMin (((k, n) :: kns)) = findMin' ((k, n), kns)
        and findMin' =
          function 
                   | ((k0, n0), []) -> (k0, n0)
                   | ((k0, n0), ((k', n') :: kns)) -> begin
                       if n' < n0 then findMin' ((k', n'), kns) else
                       findMin' ((k0, n0), kns) end;;
        let rec cover (v_, p, ((w_, ci) as wci), ccs, lab, missing) =
          begin
            chatter
            6
            (function 
                      | () -> (showPendingGoal (v_, p, ci, lab)) ^ "\n");
            cover' (contract (v_, p, ci, lab), wci, ccs, lab, missing)
            end
        and cover' =
          function 
                   | (Some (v_, p), ((w_, ci) as wci), ccs, lab, missing)
                       -> split
                          (v_, p,
                           selectCand (match_ (I.null_, v_, p, ci, ccs)),
                           wci, ccs, lab, missing)
                   | (None, wci, ccs, lab, missing)
                       -> begin
                            chatter 6 (function 
                                                | () -> "Covered\n");missing
                            end
        and split =
          function 
                   | (v_, p, None, wci, ccs, lab, missing)
                       -> begin
                            chatter 6 (function 
                                                | () -> "Covered\n");missing
                            end
                   | (v_, p, Some [], ((w_, ci) as wci), ccs, lab, missing)
                       -> begin
                            chatter
                            6
                            (function 
                                      | ()
                                          -> "No strong candidates---calculating weak candidates\n");
                            splitWeak
                            (v_, p, finitary (v_, p, w_, ci), wci, ccs, lab,
                             missing)
                            
                            end
                   | (v_, p, Some (((k, _) :: ksn)), ((w_, ci) as wci), ccs,
                      lab, missing)
                       -> begin
                          match splitVar (v_, p, k, wci)
                          with 
                               | Some cases
                                   -> covers (cases, wci, ccs, lab, missing)
                               | None
                                   -> split
                                      (v_, p, (Some ksn), wci, ccs, lab,
                                       missing)
                          end
        and splitWeak =
          function 
                   | (v_, p, [], wci, ccs, lab, missing)
                       -> begin
                            chatter
                            6
                            (function 
                                      | ()
                                          -> ("No weak candidates---case " ^
                                                (labToString lab))
                                               ^ " not covered\n");
                            ((v_, p) :: missing)
                            end
                   | (v_, p, ksn, wci, ccs, lab, missing)
                       -> split
                          (v_, p, (Some [findMin ksn]), wci, ccs, lab,
                           missing)
        and covers (cases, wci, ccs, lab, missing) =
          begin
            chatter
            6
            (function 
                      | ()
                          -> (("Found " ^ (Int.toString (List.length cases)))
                                ^ (pluralize (List.length cases, " case")))
                               ^ "\n");
            covers' (cases, 1, wci, ccs, lab, missing)
            end
        and covers' =
          function 
                   | ([], n, wci, ccs, lab, missing)
                       -> begin
                            chatter
                            6
                            (function 
                                      | ()
                                          -> ("All subcases of " ^
                                                (labToString lab))
                                               ^ " considered\n");
                            missing
                            end
                   | (((v_, p) :: cases'), n, wci, ccs, lab, missing)
                       -> covers'
                          (cases', n + 1, wci, ccs, lab,
                           cover (v_, p, wci, ccs, (Child (lab, n)), missing));;
        let rec constsToTypes =
          function 
                   | [] -> []
                   | (I.Const c :: cs')
                       -> (I.constType c :: constsToTypes cs')
                   | (I.Def d :: cs') -> (I.constType d :: constsToTypes cs');;
        let rec createCoverClause =
          function 
                   | (I.Decl (g_, d_), v_, p)
                       -> createCoverClause
                          (g_, (I.Pi ((d_, I.maybe_), v_)), p + 1)
                   | (null_, v_, p) -> (Whnf.normalize (v_, I.id), p);;
        let rec createCoverGoal (g_, vs_, p, ms) =
          createCoverGoalW (g_, Whnf.whnf vs_, p, ms)
        and createCoverGoalW =
          function 
                   | (g_, (I.Pi ((d1_, p1_), v2_), s), 0, ms)
                       -> let d1'_ = I.decSub (d1_, s)
                            in let v2'_ =
                                 createCoverGoal
                                 ((I.Decl (g_, d1'_)), (v2_, I.dot1 s), 0,
                                  ms)
                                 in (I.Pi ((d1'_, p1_), v2'_))
                   | (g_, (I.Pi (((I.Dec (_, v1_) as d_), _), v2_), s), p,
                      ms)
                       -> let x_ = Whnf.newLoweredEVar (g_, (v1_, s))
                            in createCoverGoal
                               (g_, (v2_, (I.Dot ((I.Exp x_), s))), p - 1,
                                ms)
                   | (g_, (I.Root ((I.Const cid as a), s_), s), p, ms)
                       -> (I.Root
                           (a,
                            createCoverSpine
                            (g_, (s_, s), (I.constType cid, I.id), ms)))
        and createCoverSpine =
          function 
                   | (g_, (nil_, s), _, mnil_) -> I.nil_
                   | (g_, (I.App (u1_, s2_), s),
                      (I.Pi ((I.Dec (_, v1_), _), v2_), s'), M.Mapp
                      (M.Marg (minus_, x), ms'))
                       -> let x_ = createEVar (g_, (I.EClo (v1_, s')))
                            in let s2'_ =
                                 createCoverSpine
                                 (g_, (s2_, s),
                                  (v2_, (I.Dot ((I.Exp x_), s'))), ms')
                                 in (I.App (x_, s2'_))
                   | (g_, (I.App (u1_, s2_), s), (I.Pi (_, v2_), s'), M.Mapp
                      (_, ms'))
                       -> (I.App
                           ((I.EClo (u1_, s)),
                            createCoverSpine
                            (g_, (s2_, s),
                             Whnf.whnf
                             (v2_, (I.Dot ((I.Exp ((I.EClo (u1_, s)))), s'))),
                             ms')))
                   | (g_, (I.SClo (s_, s'), s), vs_, ms)
                       -> createCoverSpine
                          (g_, (s_, I.comp (s', s)), vs_, ms);;
        end;;
    (*****************);;
    (* Strengthening *);;
    (*****************);;
    (* next section adapted from m2/metasyn.fun *);;
    (* weaken (G, a) = w'

       Invariant:
       If   a is a type family
       then G |- w' : G'
       and  forall x:A in G'  A subordinate to a
     *);;
    (* added next case, probably should not arise *);;
    (* Sun Dec 16 10:42:05 2001 -fp !!! *);;
    (*
      | weaken (I.Decl (G', D as I.BDec _), a) =
           I.dot1 (weaken (G', a))
      *);;
    (* createEVar (G, V) = X[w] where G |- X[w] : V

       Invariant:
       If G |- V : L
       then G |- X[w] : V
    *);;
    (* G |- V : L *);;
    (* G  |- w  : G'    *);;
    (* G' |- iw : G     *);;
    (* G' |- X' : V[iw] *);;
    (* was I.newEvar (G', I.EClo (V, iw))  Mon Feb 28 14:30:36 2011 --cs *);;
    (* G  |- X  : V     *);;
    (*************************);;
    (* Coverage instructions *);;
    (*************************);;
    (* Coverage instructions mirror mode spines, but they
       are computed from modes differently for input and output coverage.

       Match  --- call match and generate candidates
       Skip   --- ignore this argument for purposes of coverage checking

       For input coverage, match input (+) and skip ignore ( * ) and output (-).

       For output coverage, skip input (+), and match output (-).
       Ignore arguments ( * ) should be impossible for output coverage
    *);;
    (* inCoverInst (ms) = ci
       converts mode spine ms to cover instructions ci for input coverage
    *);;
    (* outCoverInst (ms) = ci
       converts mode spine ms to cover instructions ci for output coverage
    *);;
    (* this last case should be impossible *);;
    (* output coverage only from totality checking, where there can be *);;
    (* no undirectional ( * ) arguments *);;
    (*
      | outCoverInst (M.Mapp (M.Marg (M.Star, x), ms')) =
          Skip (outCoverInst ms')
      *);;
    (***************************);;
    (* Printing Coverage Goals *);;
    (***************************);;
    (* labels for cases for tracing coverage checker *);;
    (* ^ *);;
    (* lab.n, n >= 1 *);;
    (* we pass in the mode spine specifying coverage, but currently ignore it *);;
    (* fix to identify existential and universal prefixes *);;
    (* p > 0 *);;
    (* other cases are impossible by CGoal invariant *);;
    (*
       Coverage goals have the form {{G}} {{L}} a @ S
       where G are splittable variables
       and L are local parameters (not splittable)
    *);;
    (**********************************************);;
    (* Creating the initial input coverage goal ***);;
    (**********************************************);;
    (* buildSpine n = n; n-1; ...; 1; Nil *);;
    (* n > 0 *);;
    (* Eta-long invariant violation -kw *);;
    (* initCGoal' (a, 0, ., V) = ({x1:V1}...{xn:Vn} a x1...xn, n)
       for |- a : V and V = {x1:V1}...{xn:Vn} type

       Invariants for initCGoal' (a, k, G, V):
       G = {x1:V1}...{xk:Vk}
       V = {xk+1:Vk+1}...{xn:Vn} type
       G |- V : type
    *);;
    (* initCGoal (a) = {x1:V1}...{xn:Vn} a x1...xn
       where a : {x1:V1}...{xn:Vn} type
    *);;
    (****************);;
    (*** Matching ***);;
    (****************);;
    (* for now, no factoring --- singleton list *);;
    (* Equation G |- (U1,s1) = (U2,s2)
       Invariant:
       G |- U1[s1] : V
       G |- U2[s2] : V  for some V

       U1[s1] has no EVars (part of coverage goal)
    *);;
    (* Splitting candidates *);;
    (* Splitting candidates [k1,...,kl] are indices
       into coverage goal {xn:Vn}...{x1:V1} a M1...Mm, counting right-to-left
    *);;
    (* equations to be solved, everything matches so far *);;
    (* candidates for splitting, matching fails *);;
    (* coverage fails without candidates *);;
    (* fail () = Fail
       indicate failure without splitting candidates
     *);;
    (* failAdd (k, cands) = cands'
       indicate failure, but add k as splitting candidate
    *);;
    (* no longer matches *);;
    (* remove duplicates? *);;
    (* addEqn (e, cands) = cands'
       indicate possible match if equation e can be solved
    *);;
    (* still may match: add equation *);;
    (* already failed: ignore new constraints *);;
    (* already failed without candidates *);;
    (* matchEqns (es) = true
       iff  all equations in es can be simultaneously unified

       Effect: instantiate EVars right-hand sides of equations.
    *);;
    (* For some reason, s2 is sometimes not a patSub when it should be *);;
    (* explicitly convert if possible *);;
    (* Sat Dec  7 20:59:46 2002 -fp *);;
    (* was: unifiable (G, Us1, Us2) *);;
    (* constraints will be left in this case *);;
    (* resolveCands (cands) = cands'
       resolve to one of
         Eqns(nil) - match successful
         Fail      - no match, no candidates
         Cands(ks) - candidates ks
       Effect: instantiate EVars in right-hand sides of equations.
    *);;
    (* reversed equations Fri Dec 28 09:39:55 2001 -fp !!! *);;
    (* why is this important? --cs !!! *);;
    (* collectConstraints (Xs) = constrs
       collect all the constraints that may be attached to EVars Xs

       try simplifying away the constraints in case they are ""hard""
       disabled for now to get a truer approximation to operational semantics
    *);;
    (* constrs <> nil *);;
    (* Constraints.simplify constrs @ *);;
    (* at present, do not simplify -fp *);;
    (* checkConstraints (cands, (Q, s)) = cands'
       failure if constraints remain in Q[s] which indicates only partial match
       Q[s] is the clause head after matching the coverage goal.

       Invariants: if cands = Eqns (es) then es = nil.
    *);;
    (* This ignores LVars, because collectEVars does *);;
    (* Why is that OK?  Sun Dec 16 09:01:40 2001 -fp !!! *);;
    (* _ = nil *);;
    (* constraints remained: Fail without candidates *);;
    (* Candidate Lists *);;
    (*
       Candidate lists record constructors and candidates for each
       constructors or indicate that the coverage goal is matched.
    *);;
    (* covered---no candidates *);;
    (* cands1,..., candsn *);;
    (* addKs (cands, klist) = klist'
       add new constructor to candidate list
    *);;
    (* matchExp (G, d, (U1, s1), (U2, s2), cands) = cands'
       matches U1[s1] (part of coverage goal)
       against U2[s2] (part of clause head)
       adds new candidates to cands to return cands'
         this could collapse to Fail,
         postponed equations Eqns(es),
         or candidates Cands(ks)
       d is depth, k <= d means local variable, k > d means coverage variable

       Invariants:
       G |- U1[s1] : V
       G |- U2[s2] : V  for some V
       G = Gc, Gl where d = |Gl|
    *);;
    (* Note: I.Proj occurring here will always have the form
              I.Proj (I.Bidx (k), i) *);;
    (* No skolem constants, foreign constants, FVars *);;
    (* k1 is coverage variable, new candidate *);;
    (* otherwise fail with no candidates *);;
    (* fail with no candidates *);;
    (* because of strictness *);;
    (* k1 is coverage variable, new candidate *);;
    (* otherwise fail with no candidates *);;
    (* was: t2 in prev line, July 22, 2010 -fp -cs *);;
    (* instantiate instead of postponing because LVars are *);;
    (* only instantiated to Bidx which are rigid *);;
    (* Sun Jan  5 12:03:13 2003 -fp *);;
    (* handled in above two cases now *);;
    (*
            | (I.Proj (b1, i1), I.Proj (b2, i2)) =>
               if (i1 = i2) then
                 matchSpine (G, d, (S1, s1), (S2, s2),
                             matchBlock (G, d, b1, b2, cands))
               else fail (""block projection / block projection clash"")
            *);;
    (* k1 is splittable, new candidate *);;
    (* otherwise fail with no candidates *);;
    (* no other cases should be possible *);;
    (* eta-expand *);;
    (* eta-expand *);;
    (* next 3 cases are only for output coverage *);;
    (* not needed since we skip input arguments for output coverage *);;
    (* see comments on CoverInst -fp Fri Dec 21 20:58:55 2001 !!! *);;
    (*
      | matchExpW (G, d, (I.Pi ((D1, _), V1), s1), (I.Pi ((D2, _), V2), s2), cands) =
        let
          val cands' = matchDec (G, d, (D1, s1), (D2, s2), cands)
        in
          matchExp (I.Decl (G, D1), d+1, (V1, I.dot1 s1), (V2, I.dot1 s2), cands')
        end
      | matchExpW (G, d, (I.Pi _, _), _, cands) = fail ()
      | matchExpW (G, d, _, (I.Pi _, _), cands) = fail ()
      *);;
    (* nothing else should be possible, by invariants *);;
    (* No I.Uni, I.FgnExp, and no I.Redex by whnf *);;
    (* BDec should be impossible here *);;
    (* matchBlock now unfolded into the first case of matchExpW *);;
    (* Sun Jan  5 12:02:49 2003 -fp *);;
    (*
    and matchBlock (G, d, I.Bidx(k), I.Bidx(k'), cands) =
        if (k = k') then cands
          else fail (""block index / block index clash"")
      | matchBlock (G, d, B1 as I.Bidx(k), I.LVar (r2, I.Shift(k'), (l2, t2)), cands) =
         Updated LVar --cs Sun Dec  1 06:24:41 2002 
        let
          val I.BDec (bOpt, (l1, t1)) = I.ctxDec (G, k)
        in
          if l1 <> l2 then fail (""block index / block label clash"")
           else if k < k' then raise Bind 
           k >= k' by invariant  Sat Dec  7 22:00:41 2002 -fp 
          else let
                 val cands2 = matchSub (G, d, t1, t2, cands)
                  instantiate if matching is successful 
                  val _ = print (candsToString (cands2) ^ ""\n"") 
                  instantiate, instead of postponing because 
                  LVars are only instantiated to Bidx's which are rigid 
                  !!!BUG!!! r2 and B1 make sense in different contexts 
                  fixed by k-k' Sat Dec  7 21:12:57 2002 -fp 
                 val _ = Unify.instantiateLVar (r2, I.Bidx (k-k'))
               in
                 cands2
               end
        end
    *);;
    (* by invariant *);;
    (* matchTop (G, (a @ S1, s1), (a @ S2, s2), ci) = cands
       matches S1[s1] (spine of coverage goal)
       against S2[s2] (spine of clause head)
       skipping over `skip' arguments in cover instructions

       Invariants:
       G |- a @ S1[s1] : type
       G |- a @ S2[s2] : type
       G contains coverage variables,
       S1[s1] contains no EVars
       cover instructions ci matche S1 and S2
    *);;
    (* unify spines, skipping output and ignore arguments in modeSpine *);;
    (* fails, with no candidates since type families don't match *);;
    (* this case can only arise in output coverage *);;
    (* we do not match D1 and D2, since D1 is always an instance of D2 *);;
    (* and no splittable variables should be suggested here *);;
    (* Sat Dec 22 23:53:44 2001 -fp !!! *);;
    (* an argument that must be covered (Match) *);;
    (* an argument that need not be covered (Skip) *);;
    (* matchClause (G, (a @ S1, s1), V, ci) = cands
       as in matchTop, but r is clause
       NOTE: Simply use constant type for more robustness (see below)
    *);;
    (* changed to use subordination and strengthening here *);;
    (* Sun Dec 16 10:39:34 2001 -fp *);;
    (* val X1 = createEVar (G, I.EClo (V1, s)) *);;
    (* changed back --- no effect *);;
    (* was val X1 = I.newEVar (G, I.EClo (V1, s)) Mon Feb 28 14:37:22 2011 -cs *);;
    (* was: I.Null instead of G in line above Wed Nov 21 16:40:40 2001 *);;
    (* matchSig (G, (a @ S, s), ccs, ci, klist) = klist'
       match coverage goal {{G}} a @ S[s]
       against each coverage clause V in ccs,
       adding one new list cand for each V to klist to obtain klist'

       Invariants:
       G |- a @ S[s] : type
       V consists of clauses with target type a @ S'
       ci matches S
       klist <> Covered
    *);;
    (* matchSig' (G, (a @ S, s), ccs, ci, klist) = klist'
       as matchSig, but check if coverage goal {{G}} a @ S[s] is already matched
    *);;
    (* already covered: return *);;
    (* not yet covered: continue to search *);;
    (* matchBlocks (G, s', piDecs, V, k, i, ci, klist) = klist'
       Invariants:
       G |- s' : Gsome
       Gsome |- piDecs : ctx
       G |- V : type
       G_k = (Gsome, D1...D(i-1) piDecs)
     *);;
    (* klist <> Covered *);;
    (* matchCtx (G, s', G', V, k, ci, klist) = klist'
       Invariants:
       G |- s' : G'
       G |- V : type
       s' o ^ = ^k
       ci matches for for V = a @ S
       klist <> Covered accumulates mode spines
    *);;
    (* will always fail for input coverage *);;
    (*  G'', V' |- ^ : G''
              G |- s' : G'', V'
          *);;
    (*  G |- ^ o s' : G'' *);;
    (* G'' |- s : Gsome,
             G |- s'' : G''
             G |- s o s'' : Gsome
             Gsome |- piDecs : ctx
          *);;
    (* as matchClause *);;
    (* p > 0 *);;
    (* was val X1 = I.newEVar (G, I.EClo (V1', s')) Mon Feb 28 14:38:21 2011 -cs *);;
    (* match (., V, p, ci, I/O(ccs)) = klist
       matching coverage goal {{G}} V against coverage clauses Vi in ccs
       yields candidates klist
       no local assumptions
       Invariants:
       V = {{G}} {{L}} a @ S where |G| = p
       cover instructions ci match S
       G |- V : type
    *);;
    (************************************);;
    (*** Selecting Splitting Variable ***);;
    (************************************);;
    (* insert (k, ksn) = ksn'
       ksn is ordered list of ks (smallest index first) with multiplicities
    *);;
    (* join (ks, ksn) = ksn'
       ksn is as in function insert
    *);;
    (* selectCand (klist) = ksnOpt
       where ksOpt is an indication of coverage (NONE)
       or a list of candidates with multiplicities

       Simple heuristic: select last splitting candidate from last clause tried
       This will never pick an index variable unless necessary.
    *);;
    (* success: case is covered! *);;
    (* failure: case G,V is not covered! *);;
    (* local failure (clash) and no candidates *);;
    (* local failure but no candidates *);;
    (* found candidates ks <> nil *);;
    (*****************);;
    (*** Splitting ***);;
    (*****************);;
    (* In a coverage goal {{G}} {{L}} a @ S we instantiate each
       declaration in G with a new EVar, then split one of these variables,
       then abstract to obtain a new coverage goal {{G'}} {{L'}} a @ S'
    *);;
    (* instEVars ({x1:V1}...{xp:Vp} V, p, nil) = (V[s], [X1,...,Xn])
       where . |- s : {x1:V1}...{xp:Vp}
       and s = Xp...X1.id, all Xi are new EVars
    *);;
    (* p > 0 *);;
    (* all EVars are global *);;
    (* was  val X1 = I.newEVar (I.Null, I.EClo (V1, s))  all EVars are global 
             Mon Feb 28 14:39:15 2011 -cs *);;
    (* G0 |- t : Gsome *);;
    (* . |- s : G0 *);;
    (* p > 0 *);;
    (* new -fp Sun Dec  1 20:58:06 2002 *);;
    (* new -cs  Sun Dec  1 06:27:57 2002 *);;
    (* caseList is a list of possibilities for a variables
       to be split.  Maintained as a mutable reference so it
       can be updated in the success continuation.
    *);;
    (* createEVarSpine (G, (V, s)) = (S', (V', s'))

       Invariant:
       If   G |- s : G1   and  G1 |- V = Pi {V1 .. Vn}. W : L
       and  G1, V1 .. Vn |- W atomic
       then G |- s' : G2  and  G2 |- V' : L
       and  S = X1; ...; Xn; Nil
       and  G |- W [1.2...n. s o ^n] = V' [sjfh']
       and  G |- S : V [s] >  V' [s']
    *);;
    (* changed to use createEVar? *);;
    (* Sun Dec 16 10:36:59 2001 -fp *);;
    (* s = id *);;
    (* G |- V1[s] : L *);;
    (* Uni or other cases should be impossible *);;
    (* createAtomConst (G, c) = (U', (V', s'))

       Invariant:
       If   S |- c : Pi {V1 .. Vn}. V
       then . |- U' = c @ (X1; .. Xn; Nil)
       and  . |- U' : V' [s']
    *);;
    (* mod: m2/metasyn.fun allows skolem constants *);;
    (* createAtomBVar (G, k) = (U', (V', s'))

       Invariant:
       If   G |- k : Pi {V1 .. Vn}. V
       then . |- U' = k @ (Xn; .. Xn; Nil)
       and  . |- U' : V' [s']
    *);;
    (* end m2/metasyn.fun *);;
    (* createAtomProj (G, #i(l), (V, s)) = (U', (V', s'))

       Invariant:
       If   G |- #i(l) : Pi {V1 .. Vn}. Va
       and  G |- Pi {V1..Vn}. Va = V[s] : type
       then . |- U' = #i(l) @ (X1; .. Xn; Nil)
       and  . |- U' : V' [s']
    *);;
    (* createEVarSub G' = s

       Invariant:
       If   . |- G' ctx
       then . |- s : G' and s instantiates each x:A with an EVar . |- X : A

       Update: Always use empty context. Sat Dec  8 13:19:58 2001 -fp
    *);;
    (* was   val V' = I.EClo (V, s)
                   val X = I.newEVar (I.Null, V') Mon Feb 28 15:32:09 2011 --cs *);;
    (* hack *);;
    (* blockCases (G, Vs, B, (Gsome, piDecs), sc) =

       If G |- V[s] : type
          . |- Gsome ctx and Gsome |- piDecs decList
       then sc is called for any x:A in piDecs such thtat
            G |- V[s] = A[t] : type
            where t instantiates variable in Gsome with new EVars
    *);;
    (* . |- t : Gsome *);;
    (* was: the above, using t' for t below *);;
    (*  BUG. Breach in the invariant:
                         G |- sk : .
                         . |- t: Gsome
                         G <> .

                         replace t by t' in I.newLVar (sk, (cid, t))
                      --cs Fri Jan  3 11:07:41 2003 *);;
    (* G |- t' : Gsome *);;
    (* G |- t : G' and G' |- ({_:V'},piDecs) decList *);;
    (* so G |- V'[t'] : type *);;
    (* will trail *);;
    (* will trail *);;
    (* will trail *);;
    (* splitEVar (X, W, sc) = ()

       calls sc () for all cases, after instantiation of X
       W are the currently possible worlds
    *);;
    (* was
   fun lowerSplit (G, Vs, W, sc, print) = lowerSplitW (G, Whnf.whnf Vs, W, sc, print)
    and lowerSplitW (G, Vs as (I.Root (I.Const a, _), s), W, sc, pr) =
        let
        val _ = print (""Consider P cases for ""  ^ Print.expToString (G, I.EClo Vs) ^ ""\n"")
val _ = pr () 
          val _ = paramCases (G, Vs, I.ctxLength G, sc)  will trail 
        val _ = print (""Consider W cases for ""  ^ Print.expToString (G, I.EClo Vs) ^ ""\n"")
val _ = pr () 
          val _ = worldCases (G, Vs, W, sc)  will trail 
        val _ = print (""Consider C cases for ""  ^ Print.expToString (G, I.EClo Vs) ^ ""\n"") 
          val _ = constCases (G, Vs, Index.lookup a, sc)  will trail 
        in
          ()
        end
      | lowerSplitW (G, (I.Pi ((D, P), V), s), W, sc, print) =
        let
          val D' = I.decSub (D, s)
        in
          lowerSplit (I.Decl (G, D'), (V, I.dot1 s), W, fn U => sc (I.Lam (D', U)), print)
        end

   fun splitEVar ((X as I.EVar (_, GX, V, _)), W, sc, print) =  GX = I.Null 
         lowerSplit (I.Null, (V, I.id), W,
                      fn U => if Unify.unifiable (I.Null, (X, I.id), (U, I.id))
                                then sc ()
                              else (), print)
    Mon Feb 28 14:49:04 2011 -cs *);;
    (* abstract (V, s) = V'
       where V' = {{G}} Vs' and G abstracts over all EVars in V[s]
       in arbitrary order respecting dependency

       Invariants: . |- V[s] : type
       Effect: may raise Constraints.Error (constrs)
     *);;
    (* splitVar ({{G}} V, p, k, W) = SOME [{{G1}} V1 ,..., {{Gn}} Vn]
                                  or NONE
       where {{Gi}} Vi are new coverage goals obtained by
       splitting kth variable in G, counting right-to-left.

       returns NONE if splitting variable k fails because of constraints

       W are the worlds defined for current predicate

       Invariants:
       |G| = p
       k <= |G|
       G |- V : type
       {{Gi}} Vi cover {{G}} V
    *);;
    (* split on k'th variable, counting from innermost *);;
    (* may raise Constraints.Error *);;
    (* Constraints.Error could be raised by abstract *);;
    (**********************);;
    (* Finitary Splitting *);;
    (**********************);;
    (*
       A splittable variable X : V is called finitary
       if there are finitely many alternatives for V.
       This means there are finitely many (including 0)
       constructors (possibly including local variables) such that
       all free variables in the argument are not recursive
       with the target type of V.

       Splitting such variables can never lead to non-termination.
    *);;
    (* Stolen from abstract.fun *);;
    (* foreign expression probably should not occur *);;
    (* but if they do, variable occurrences don't count *);;
    (* occursInExp (k, Whnf.normalize (#toInternal(ops) (), I.id)) *);;
    (* no case for Redex, EVar, EClo *);;
    (* no case for SClo *);;
    (* occursInMatchPos (k, U, ci) = true
       if k occur in U in a matchable position according to the coverage
       instructions ci
    *);;
    (* instEVarsSkip ({x1:V1}...{xp:Vp} V, p, nil, ci) = (V[s], [X1,...,Xn])
       where . |- s : {x1:V1}...{xp:Vp}
       and s = Xp...X1.id, all Xi are new EVars that actually occur in a ""Match"" argument
       and ci are the coverage instructions (Match or Skip) for the target type of V
    *);;
    (* p > 0 *);;
    (* all EVars are global *);;
    (* was val X1 = I.newEVar (I.Null, I.EClo (V1, s))  all EVars are global 
             Mon Feb 28 15:25:42 2011 --cs *);;
    (* G0 |- t : Gsome *);;
    (* . |- s : G0 *);;
    (* p > 0 *);;
    (* -fp Sun Dec  1 21:09:38 2002 *);;
    (* -cs Sun Dec  1 06:30:59 2002 *);;
    (* if contraints remain, consider recursive and thereby unsplittable *);;
    (* recursive X = true
       iff the instantiation of X : {{G}} a @ S contains an
           EVar Y : {{G'}} b @ S such that a <|= b

       This means there is no guarantee that X : {{G}} a @ S has only
       a finite number of instances
    *);;
    (* GX = I.Null*);;
    (* is this always true? --cs!!!*);;
    (* LVars are ignored here.  OK because never splittable? *);;
    (* Sat Dec 15 22:42:10 2001 -fp !!! *);;
    (* finitary1 (X, k, W, f, cands)
        = ((k, n)::cands) if X is finitary with n possibilities
        = cands if X is not finitary
    *);;
    (* The function f has been added to ensure that k is splittable without
       constraints.   In the previous version, this check was not performed.
       nat : type.
       z : nat.
       s : nat -> nat.

       eqz :  nat -> type.
       eqz_z : eqz z.

       unit : type.
       * : unit.

       test : {f : unit -> nat} eqz (f * ) -> type.
       %worlds () (test _ _).
       %covers test +F +Q.  %% loops!
        Counterexample due to Andrzej.  Fix due to Adam.
        Mon Oct 15 15:08:25 2007 --cs
    *);;
    (* was Mon Feb 28 15:29:36 2011 -cs
    fun finitary1 (X as I.EVar(r, I.Null, VX, _), k, W, f, cands, print) =
        ( resetCount () ;
          chatter 7 (fn () => ""Trying "" ^ Print.expToString (I.Null, X) ^ "" : ""
                     ^ Print.expToString (I.Null, VX) ^ "".\n"") ;
          ( splitEVar (X, W, fn () => (f (); if recursive X
                                        then raise NotFinitary
                                      else incCount ()), print) ;
            chatter 7 (fn () => ""Finitary with "" ^ Int.toString (getCount ()) ^ "" candidates.\n"");

            (k, getCount ())::cands )
           handle NotFinitary => ( chatter 7 (fn () => ""Not finitary.\n"");
                                   cands )
                 | Constraints.Error (constrs) =>
                                 ( chatter 7 (fn () => ""Inactive finitary split.\n"");
                                   cands )
        )
    *);;
    (* finitarySplits (XsRev, k, W, cands) = [(k1,n1),...,(km,nm)]@cands
       where all ki are finitary with ni possibilities for X(i+k)
    *);;
    (* parameter blocks can never be split *);;
    (* finitary ({{G}} V, p, W) = [(k1,n1),...,(km,nm)]
       where ki are indices of splittable variables in G with ni possibilities
       and |G| = p
       and ci are the coverage instructions for the target type of V
    *);;
    (***********************************);;
    (* Contraction based on uniqueness *);;
    (***********************************);;
    (* eqExp (U[s], U'[s']) = true iff G |- U[s] == U'[s'] : V
       Invariants:
         G |- U[s] : V
         G |- U'[s'] : V
         U[s], U'[s'] contain no EVars
       Note that the typing invariant is satisfied because
       input arguments can only depend on other input arguments,
       but not undetermined or output arguments.
       Similar remarks apply to functions below
    *);;
    (* eqInpSpine (ms, S1[s1], S2[s2]) = true
       iff U1[s1] == U2[s2] for all input (+) arguments in S1, S2
       according to uniqueness mode spine ms
       Invariants: typing as in eqExp, ms ~ S1, ms ~ S2
    *);;
    (* ignore Star, Minus, Minus1 *);;
    (* other cases should be impossible since spines must match *);;
    (* eqInp (G, k, a, S[s], ms) = [k1+k,...,kn+k]
       where k1,...,kn are the deBruijn indices of those declarations
       ki:a @ Si in such that G0 |- Si[^ki+k] == S[s] on all input arguments
       according to mode spine ms.
       Here G = ...kn:a @ Sn, ..., k1:a @ S1, ...
    *);;
    (* defined type families disallowed here *);;
    (* other cases should be impossible *);;
    (* contractionCands (G, k) = [[k11,...,k1{n1}],...,[km1,...,km{nm}]]
       where each [kj1,...,kj{nj}] are deBruijn indices in G (counting from right)
       such that kji:aj @ Sji ... kj{nj}:aj @ Sj{nj} and
       Sji...Sj{nj} agree on their input arguments according to the
       uniqueness mode spine for aj
    *);;
    (* defined type families disallowed here *);;
    (* using only one uniqueness declaration per type family *);;
    (* ignore Pi --- contraction cands unclear *);;
    (* ignore blocks --- contraction cands unclear *);;
    (* isolateSplittable ((G0, {{G1}}V, p) = ((G0@G1), V) where |G1| = p
       This isolates the splittable variable G1@G1 from an old-style
       coverage goal ({{G}}V, p)
    *);;
    (* unifyUOutSpine (ms, S1[s1], S2[s2]) = true
       iff U1[s1] == U2[s2] for all unique output (-1) arguments in S1, S2
       according to uniqueness mode spine ms
       Invariants: the input arguments in S1[s1] and S2[s2] must be known
          to be equal, ms ~ S1, ms ~ S2
       Effect: EVars in S1[s1], S2[s2] are instantianted, both upon
          failure and success
    *);;
    (* will have effect! *);;
    (* if mode = + already equal by invariant; otherwise ignore *);;
    (* Nil/App or App/Nil cannot occur by invariants *);;
    (* unifyUOuttype (a @ S1, a @ S2) = true
       iff S1 and S2 unify on all unique output (-1) arguments in S1, S2
       according to uniqueness mode declaration for a (both args must have same a)
       Invariants: the input args in S1, S2 must be known to be equal
          and a must have a uniqueness mode
       Effect: Evars may be instantiated by unification
    *);;
    (* a1 = a2 by invariant *);;
    (* must succeed by invariant *);;
    (* must be constant-headed roots by invariant *);;
    (* unifyUOutEvars (X1, X2) = true
       iff . |- X1 : a @ S1, . |- X2 : a @ S2 and the unique output arguments
       in V1 and V2 unify
       Invariants: the input args in S1, S2, must be known to be equal
         Both types start with the same a, a must have a uniqueness mode
       Effect: Evars may be instantiated by unification
    *);;
    (* G1 = G2 = Null *);;
    (* unifyUOut2 ([X1,...,Xp], k1, k2) = (see unifyOutEvars (X{k1}, X{k2})) *);;
    (* unifyOut1 ([X1,...,Xp], [k1, k2, ..., kn] = true
       if X{k1} ""=="" X{k2} ""=="" ... ""=="" X{kn} according to unifyOutEvars
    *);;
    (* unifyOut ([X1,...,Xp], [[k11,...,k1{n1}],...,[km1,...,km{nm}]]) = true
       if unifyOut1 ([X1,...,Xp], [kj1,...,kj{nj}]) for each j
    *);;
    (* contractAll ({{G}}V, p, ucands) = SOME(V',p')
       iff (V',p') is the result of contracting unique output arguments
           according to contraction candidates ucands
           of variables in G where all input arguments agree
       returns NONE if unique output arguments are non-unifiable
       may be the identity if output arguments are already identity
          or unsolvable constraints during contraction
       Invariants: p = |G| (G contains the splittable variables)
    *);;
    (* as in splitVar *);;
    (* as in splitVar, may raise Constraints.Error *);;
    (* unique outputs not simultaneously unifiable *);;
    (* contract ({{G}}V0, p, ci, lab) = SOME(V',p')
       iff (V',p') is the result of contracting unique output arguments
           of variables in G where all input arguments agree
       returns NONE if unique output arguments are non-unifiable
       may be the identity if output arguments are already identity
          or unsolvable constraints during contraction
       ci and lab are used for printing
       Invariants: p = |G| (G contains the splittable variables)
    *);;
    (* ignore body of coverage goal *);;
    (* no progress if constraints remain *);;
    (* no candidates, no progress *);;
    (*********************);;
    (* Coverage Checking *);;
    (*********************);;
    (* findMin ((k1,n1),...,(km,nm)) = (ki,ni)
       where ni is the minimum among the n1,...,nm
       Invariant: m >= 1
    *);;
    (* need to improve tracing with higher chatter levels *);;
    (* ccs = covering clauses *);;
    (* cover (V, p, (W, ci), ccs, lab, missing) = missing'
       covers ([(V1,p1),...,(Vi,pi)], (W, ci), ccs, missing) = missing'

       check if Match arguments (+ for input, - for output) in V or all Vi, respectively,
       are covered by clauses ccs, adding omitted cases to missing to yield missing'.

       V = {{G}} {{L}} a @ S where |G| = p and G contains the splittable
       variables while L contains the local parameters

       W are the worlds for type family a
       ci are the cover instructions matching S

       lab is the label for the current goal for tracing purposes
    *);;
    (* V is covered by unique output inconsistency *);;
    (* V is covered: return missing patterns from other cases *);;
    (* no strong candidates: check for finitary splitting candidates *);;
    (* some candidates: split first candidate, ignoring multiplicities *);;
    (* candidates are in reverse order, so non-index candidates are split first *);;
    (* splitVar shows splitting as it happens *);;
    (* splitting variable k generated constraints *);;
    (* try other candidates *);;
    (* ksn <> nil *);;
    (* commit to the minimal candidate, since no constraints can arise *);;
    (******************);;
    (* Input Coverage *);;
    (******************);;
    (* constsToTypes [c1,...,cn] = [V1,...,Vn] where ci:Vi.
       Generates coverage clauses from signature.
    *);;
    (*******************);;
    (* Output Coverage *);;
    (*******************);;
    (* createCoverClause (G, V, 0) = ({{G}} V, |G|)
       where {{G}} V is in NF
    *);;
    (* createCoverGoal (., ({{G}} {{GL}} a @ S, s), p, ms) = V' with |G| = p
       createCoverGoal (GL, (a @ S, s), 0, ms) = a @ S'
       createCoverSpine ((S, s), (V', s'), ms) = S'

       where all variables in G are replaced by new EVars in V to yield V'
       and output arguments in S are replaced by new EVars in V to yield V'

       G are the externally quantified variables
       GL are the locally introduced parameter for the current subgoal a @ S

       Invariants: . |- ({{G}} {{GL}} a @ S)[s] : type
                   |G| = p
                   ms matches S
                   . | S[s] : V'[s'] > type
                   . |- V'[s'] : type
    *);;
    (* p > 0, G = I.Null *);;
    (* was  val X = I.newEVar (G, I.EClo (V1, s))  Mon Feb 28 15:33:52 2011 -cs *);;
    (* s = id, p >= 0 *);;
    (* replace output argument by new variable *);;
    (* strengthen G based on subordination *);;
    (* leave input ( + ) arguments as they are, ignore ( * ) impossible *);;
    let rec checkNoDef a =
      begin
      match I.sgnLookup a
      with 
           | I.ConDef _
               -> raise
                  ((Error
                    (("Coverage checking " ^ (N.qidToString (N.constQid a)))
                       ^ ":\ntype family must not be defined.")))
           | _ -> ()
      end;;
    (* checkCovers (a, ms) = ()
       checks coverage for type family a with respect to mode spine ms
       Effect: raises Error (msg) otherwise
    *);;
    let rec checkCovers (a, ms) =
      let _ =
        chatter
        4
        (function 
                  | ()
                      -> ("Input coverage checking family " ^
                            (N.qidToString (N.constQid a)))
                           ^ "\n")
        in let _ = checkNoDef a
             in let _ =
                  try Subordinate.checkNoDef a
                  with 
                       | Subordinate.Error msg
                           -> raise
                              ((Error
                                ((("Coverage checking " ^
                                     (N.qidToString (N.constQid a)))
                                    ^ ":\n")
                                   ^ msg)))
                  in let (v0_, p) = initCGoal a
                       in let _ = begin
                            if ! Global.doubleCheck then
                            TypeCheck.typeCheck
                            (I.null_, (v0_, (I.Uni I.type_))) else () end
                            in let _ = CSManager.reset ()
                                 in let cIn = inCoverInst ms
                                      in let cs = Index.lookup a
                                           in let ccs = constsToTypes cs
                                                in let w_ = W.lookup a
                                                     in let v0_ =
                                                          createCoverGoal
                                                          (I.null_,
                                                           (v0_, I.id), p,
                                                           ms)
                                                          in let (v0_, p) =
                                                               abstract
                                                               (v0_, I.id)
                                                               in let missing
                                                                    =
                                                                    cover
                                                                    (v0_, p,
                                                                    (w_, cIn),
                                                                    input_
                                                                    ccs, Top,
                                                                    [])
                                                                    in 
                                                                    let _ =
                                                                    begin
                                                                    match missing
                                                                    with 
                                                                    
                                                                    | 
                                                                    [] -> ()
                                                                    | 
                                                                    (_ :: _)
                                                                    -> 
                                                                    raise
                                                                    ((Error
                                                                    (("Coverage error --- missing cases:\n"
                                                                    ^
                                                                    (missingToString
                                                                    (missing,
                                                                    ms))) ^
                                                                    "\n")))
                                                                    end
                                                                    (* all cases covered *)
                                                                    in ()
                                                                    (* convert mode spine to cover instructions *)(* lookup constants defining a *)(* calculate covering clauses *)(* world declarations for a; must be defined *)(* replace output by new EVars *)(* abstract will double-check *);;
    (* checkOut (G, (V, s)) = ()
       checks if the most general goal V' is locally output-covered by V
       Effect: raises Error (msg) otherwise
    *);;
    let rec checkOut (g_, (v_, s)) =
      let a = I.targetFam v_
        in let Some ms = ModeTable.modeLookup a
             in let cOut = outCoverInst ms
                  in let (v'_, q) =
                       createCoverClause (g_, (I.EClo (v_, s)), 0)
                       in let _ = begin
                            if ! Global.doubleCheck then
                            TypeCheck.typeCheck
                            (I.null_, (v'_, (I.Uni I.type_))) else () end
                            in let v0_ =
                                 createCoverGoal
                                 (I.null_, (v'_, I.id), q, ms)
                                 in let (v0'_, p) = abstract (v0_, I.id)
                                      in let w_ = W.lookup a
                                           in let missing =
                                                cover
                                                (v0'_, p, (w_, cOut),
                                                 output_ (v'_, q), Top, [])
                                                in let _ =
                                                     begin
                                                     match missing
                                                     with 
                                                          | [] -> ()
                                                          | (_ :: _)
                                                              -> raise
                                                                 ((Error
                                                                   (("Output coverage error --- missing cases:\n"
                                                                    ^
                                                                    (missingToString
                                                                    (missing,
                                                                    ms))) ^
                                                                    "\n")))
                                                     end in ()
                                                     (* must be defined and well-moded *)(* determine cover instructions *)(* abstract all variables in G *)(* replace output by new EVars *)(* abstract will double-check *);;
    (**********************************************);;
    (* New code for coverage checking of Tomega   *);;
    (* Started Sun Nov 24 11:02:25 2002  -fp      *);;
    (* First version Tue Nov 26 19:29:12 2002 -fp *);;
    (**********************************************);;
    (* cg = CGoal (G, S)  with G |- S : {{G'}} type *);;
    type coverGoal_ = | CGoal of I.dctx * I.spine_ ;;
    (* cc = CClause (Gi, Si) with  Gi |- Si : {{G}} type *);;
    type coverClause_ = | CClause of I.dctx * I.spine_ ;;
    let rec formatCGoal (CGoal (g_, s_)) =
      let _ = N.varReset I.null_
        in (F.HVbox
            ([Print.formatCtx (I.null_, g_); F.break_; F.break_;
              (F.String "|-"); F.space_] @ (Print.formatSpine (g_, s_))));;
    let rec showPendingCGoal (CGoal (g_, s_), lab) =
      F.makestring_fmt
      ((F.Hbox
        [(F.String (labToString lab)); F.space_; (F.String "?- ");
         formatCGoal ((CGoal (g_, s_))); (F.String ".")]));;
    let rec showCClause (CClause (g_, s_)) =
      let _ = N.varReset I.null_
        in F.makestring_fmt
           ((F.HVbox ([(F.String "!- ")] @ (Print.formatSpine (g_, s_)))));;
    let rec showSplitVar (CGoal (g_, s_), k) =
      let _ = N.varReset I.null_
        in let I.Dec (Some x, _) = I.ctxLookup (g_, k)
             in (("Split " ^ x) ^ " in ") ^
                  (F.makestring_fmt ((F.HVbox (Print.formatSpine (g_, s_)))));;
    (* newEVarSubst (G, G') = s
       Invariant:   If G = xn:Vn,...,x1:V1
                  then s = X1...Xn.^k
                     G |- s : G'
    *);;
    let rec newEVarSubst =
      function 
               | (g_, null_) -> (I.Shift (I.ctxLength g_))
               | (g_, I.Decl (g'_, (I.Dec (_, v_) as d_)))
                   -> let s' = newEVarSubst (g_, g'_)
                        in let x_ = Whnf.newLoweredEVar (g_, (v_, s'))
                             in (I.Dot ((I.Exp x_), s'))
                             (* was val V' = I.EClo (V, s')
                 val X = I.newEVar (G, V') Mon Feb 28 15:34:31 2011 -cs *)
               | (g_, I.Decl (g'_, (I.NDec _ as d_)))
                   -> let s' = newEVarSubst (g_, g'_)
                        in (I.Dot (I.undef_, s'))
               | (g_, I.Decl (g'_, (I.BDec (_, (b, t)) as d_)))
                   -> let s' = newEVarSubst (g_, g'_)
                        in let l1_ = I.newLVar (s', (b, t))
                             in (I.Dot ((I.Block l1_), s'))
                             (* was  val L1 = I.newLVar (I.Shift(0), (b, I.comp(t, s')))
             --cs Fri Jul 23 16:39:27 2010 *)(* -cs Fri Jul 23 16:35:04 2010  FPCHECK *)(* L : Delta[t][G'] *)(* G |- s : G'  G |- L[s'] : V[s]
             G |- (L[s'].s : G', V *)(* -fp Sun Dec  1 21:10:45 2002 *)(* -cs Sun Dec  1 06:31:23 2002 *);;
    (* ADec should be impossible *);;
    (* checkConstraints (G, Si[ti], cands) = cands'
       failure if constraints remain in Q[s] which indicates only partial match
       Q[s] is the clause head after matching the coverage goal.

       Invariants: if cands = Eqns (es) then es = nil.
    *);;
    (* This ignores LVars, because collectEVars does *);;
    (* Why is that OK?  Sun Dec 16 09:01:40 2001 -fp !!! *);;
    let rec checkConstraints =
      function 
               | (g_, (si_, ti), Cands ks) -> cands_ ks
               | (g_, (si_, ti), Fail) -> Fail
               | (g_, (si_, ti), Eqns _)
                   -> let xs_ =
                        Abstract.collectEVarsSpine (g_, (si_, ti), [])
                        in let constrs = collectConstraints xs_
                             in begin
                                match constrs
                                with 
                                     | [] -> eqns_ []
                                     | _ -> fail "Remaining constraints"
                                end
                             (* constraints remained: Fail without candidates *)(* _ = nil *);;
    (* matchClause (cg, (Si, ti)) = klist
       matching coverage goal cg against instantiated coverage clause Si[ti]
       yields splitting candidates klist
    *);;
    let rec matchClause (CGoal (g_, s_), (si_, ti)) =
      let cands1 = matchSpine (g_, 0, (s_, I.id), (si_, ti), eqns_ [])
        in let cands2 = resolveCands cands1
             in let cands3 = checkConstraints (g_, (si_, ti), cands2)
                  in cands3;;
    (* matchClauses (cg, ccs, klist) = klist'
       as in match, with accumulator argument klist
    *);;
    let rec matchClauses =
      function 
               | (cg, [], klist) -> klist
               | ((CGoal (g_, s_) as cg), (CClause (gi_, si_) :: ccs), klist)
                   -> let ti = newEVarSubst (g_, gi_)
                        in let cands =
                             CSManager.trail
                             (function 
                                       | () -> matchClause (cg, (si_, ti)))
                             in matchClauses' (cg, ccs, addKs (cands, klist))
                             (* G |- ti : Gi *)
    and matchClauses' =
      function 
               | (cg, ccs, covered_) -> covered_
               | (cg, ccs, (CandList _ as klist))
                   -> matchClauses (cg, ccs, klist);;
    (* match (cg, ccs) = klist
       matching coverage goal cg against coverage clauses ccs
       yields candidates klist
    *);;
    let rec match_ (CGoal (g_, s_), ccs) =
      matchClauses ((CGoal (g_, s_)), ccs, candList_ []);;
    (* abstractSpine (S, s) = CGoal (G, S')
       Invariant: G abstracts all EVars in S[s]
       G |- S' : {{G'}}type
    *);;
    let rec abstractSpine (s_, s) =
      let (g'_, s'_) = Abstract.abstractSpine (s_, s)
        in let namedG' = N.ctxName g'_
             in let _ = begin
                  if ! Global.doubleCheck then TypeCheck.typeCheckCtx namedG'
                  (* TypeCheck.typeCheckSpine (namedG', S') *) else () end
                  in (CGoal (namedG', s'_)) (* for printing purposes *);;
    (* kthSub (X1...Xn.^0, k) = Xk
       Invariant: 1 <= k <= n
       Xi are either EVars or to be ignored
    *);;
    let rec kthSub =
      function 
               | (I.Dot (I.Exp x_, s), 1) -> x_
               | (I.Dot (_, s), k) -> kthSub (s, k - 1);;
    (* subToXsRev (X1...Xn.^0) = [Xiopt,...,Xnopt]
       Invariant: Xi are either EVars (translate to SOME(Xi))
                  or not (translate to NONE)
    *);;
    let rec subToXsRev =
      function 
               | I.Shift 0 -> []
               | I.Dot (I.Exp x_, s) -> ((Some x_) :: subToXsRev s)
               | I.Dot (_, s) -> (None :: subToXsRev s)(* n = 0 *);;
    (* caseList is a list of possibilities for a variables
       to be split.  Maintained as a mutable reference so it
       can be updated in the success continuation.
    *);;
    open! struct
            let caseList : coverGoal_ list ref = ref [];;
            end;;
    let rec resetCases () = caseList := [];;
    let rec addCase cg = caseList := ((cg :: ! caseList));;
    let rec getCases () = ! caseList;;
    (* splitVar (CGoal(G, S), k, w) = SOME [cg1,...,cgn]
                                  or NONE
       where cgi are new coverage goals obtained by
       splitting kth variable in G, counting right-to-left.

       returns NONE if splitting variable k fails because of constraints

       w are the worlds defined for current predicate

       Invariants:
       k <= |G|
       G |- S : {{G'}} type
       cgi cover cg
    *);;
    let rec splitVar ((CGoal (g_, s_) as cg), k, w) =
      try let _ = chatter 6 (function 
                                      | () -> (showSplitVar (cg, k)) ^ "\n")
            in let s = newEVarSubst (I.null_, g_)
                 in let x_ = kthSub (s, k)
                      in let _ = resetCases ()
                           in let _ =
                                splitEVar
                                (x_, w,
                                 function 
                                          | ()
                                              -> addCase
                                                 (abstractSpine (s_, s)))
                                in (Some (getCases ()))
                                (* for splitting, EVars are always global *)(* G = xn:V1,...,x1:Vn *)(* s = X1....Xn.^0, where . |- s : G *)(* starts with k = 1 (a la deBruijn) *)
      with 
           | Constraints.Error constrs
               -> begin
                    chatter
                    7
                    (function 
                              | ()
                                  -> ("Inactive split:\n" ^
                                        (Print.cnstrsToString constrs))
                                       ^ "\n");
                    None
                    end
      (* Constraints.Error could be raised by abstract *);;
    (* finitary (CGoal (G, S), W) = [(k1,n1),...,(km,nm)]
       where ki are indices of splittable variables in G with ni possibilities
    *);;
    let rec finitary (CGoal (g_, s_), w) =
      let s = newEVarSubst (I.null_, g_)
        in let xsRev_ = subToXsRev s
             in finitarySplits
                (xsRev_, 1, w, function 
                                        | () -> abstractSpine (s_, s), [])
             (* G = xn:Vn,...,x1:V1 *)(* for splitting, EVars are always global *)(* s = X1...Xn.^0,  . |- S : G *)(* XsRev = [SOME(X1),...,SOME(Xn)] *);;
    (***************);;
    (* Contraction *);;
    (***************);;
    (* for explanation, see contract and contractAll above *);;
    let rec contractAll (CGoal (g_, s_), ucands) =
      let s = newEVarSubst (I.null_, g_)
        in let xsRev_ = subToXsRev s in begin
             if unifyUOut (xsRev_, ucands) then
             (Some (abstractSpine (s_, s))) else None end
             (* as in splitVar, may raise Constraints.Error *)(* for unif, EVars are always global *);;
    let rec contract ((CGoal (g_, s_) as cg), lab) =
      let ucands = contractionCands (g_, 1)
        in let n = List.length ucands
             in let _ = begin
                  if n > 0 then
                  chatter
                  6
                  (function 
                            | ()
                                -> ((("Found " ^ (Int.toString n)) ^
                                       " contraction ")
                                      ^ (pluralize (n, "candidate")))
                                     ^ "\n")
                  else () end
                  in let cgOpt' = begin
                       if n > 0 then
                       try contractAll (cg, ucands)
                       with 
                            | Constraints.Error _
                                -> begin
                                     chatter
                                     6
                                     (function 
                                               | ()
                                                   -> "Contraction failed due to constraints\n");
                                     (Some cg)
                                     end
                       else (Some cg) end
                       (* no progress if constraints remain *)
                       in let _ =
                            begin
                            match cgOpt'
                            with 
                                 | None
                                     -> chatter
                                        6
                                        (function 
                                                  | ()
                                                      -> "Case impossible: conflicting unique outputs\n")
                                 | Some cg'
                                     -> chatter
                                        6
                                        (function 
                                                  | ()
                                                      -> (showPendingCGoal
                                                          (cg', lab)) ^ "\n")
                            end in cgOpt' (* no candidates, no progress *);;
    (* cover (cg, w, ccs, lab, missing) = missing'
       covers ([cg1,...,cgn], w, ccs, missing) = missing'

       Check if cover goal cg (or [cg1,..,cgn]) are covered by
       cover clauses ccs, adding missing cases to missing to yield missing'

       cg = CGoal (G, S) where G contains the splittable variables
       cci = CClause (Gi, Si) where Gi contains essentially existential variables

       w are the worlds for the principal type family

       lab is the label for the current goal for tracing purposes
    *);;
    let rec cover (cg, w, ccs, lab, missing) =
      begin
        chatter 6 (function 
                            | () -> (showPendingCGoal (cg, lab)) ^ "\n");
        cover' (contract (cg, lab), w, ccs, lab, missing)
        end
    and cover' =
      function 
               | (Some cg, w, ccs, lab, missing)
                   -> let cands = match_ (cg, ccs)
                        in let cand = selectCand cands
                             in split (cg, cand, w, ccs, lab, missing)
                             (* determine splitting candidates *)(* select one candidate *)
               | (None, w, ccs, lab, missing)
                   -> begin
                        chatter 6 (function 
                                            | () -> "Covered\n");missing
                        end(* cg is covered by unique output inconsistency *)
    and split =
      function 
               | (cg, None, w, ccs, lab, missing)
                   -> begin
                        chatter 6 (function 
                                            | () -> "Covered\n");missing
                        end
               | (cg, Some [], w, ccs, lab, missing)
                   -> begin
                        chatter
                        6
                        (function 
                                  | ()
                                      -> "No strong candidates --- calculating weak candidates\n");
                        splitWeak
                        (cg, finitary (cg, w), w, ccs, lab, missing)
                        end
               | (cg, Some (((k, _) :: ksn)), w, ccs, lab, missing)
                   -> begin
                        chatter
                        6
                        (function 
                                  | ()
                                      -> ("Splitting on " ^ (Int.toString k))
                                           ^ "\n");
                        begin
                        match splitVar (cg, k, w)
                        with 
                             | Some cases
                                 -> covers (cases, w, ccs, lab, missing)
                             | None
                                 -> begin
                                      chatter
                                      6
                                      (function 
                                                | ()
                                                    -> "Splitting failed due to generated constraints\n");
                                      split
                                      (cg, (Some ksn), w, ccs, lab, missing)
                                      end
                        end
                        end(* splitVar shows splitting as it happens *)(* candidates are in reverse order, so non-index candidates are split first *)(* some candidates: split first candidate, ignoring multiplicities *)(* no strong candidates: check for finitary splitting candidates *)(* cg is covered: return missing patterns from other cases *)
    and splitWeak =
      function 
               | (cg, [], w, ccs, lab, missing)
                   -> begin
                        chatter
                        6
                        (function 
                                  | ()
                                      -> ("No weak candidates---case " ^
                                            (labToString lab))
                                           ^ " not covered\n");
                        (cg :: missing)
                        end
               | (cg, ksn, w, ccs, lab, missing)
                   -> split (cg, (Some [findMin ksn]), w, ccs, lab, missing)(* ksn <> nil *)
    and covers (cases, w, ccs, lab, missing) =
      begin
        chatter
        6
        (function 
                  | ()
                      -> (("Found " ^ (Int.toString (List.length cases))) ^
                            (pluralize (List.length cases, " case")))
                           ^ "\n");
        covers' (cases, 1, w, ccs, lab, missing)
        end
    and covers' =
      function 
               | ([], n, w, ccs, lab, missing)
                   -> begin
                        chatter
                        6
                        (function 
                                  | ()
                                      -> ("All subcases of " ^
                                            (labToString lab))
                                           ^ " considered\n");
                        missing
                        end
               | ((cg :: cases'), n, w, ccs, lab, missing)
                   -> let missing1 =
                        cover (cg, w, ccs, child_ (lab, n), missing)
                        in covers' (cases', n + 1, w, ccs, lab, missing1);;
    (* substToSpine' (s, G, T) = S @ T
       If   G' |- s : G
       then G' |- S : {{G}} a >> a  for arbitrary a
       {{G}} erases void declarations in G
    *);;
    let rec substToSpine' =
      function 
               | (I.Shift n, null_, t_) -> t_
               | (I.Shift n, (I.Decl _ as g_), t_)
                   -> substToSpine'
                      ((I.Dot ((I.Idx (n + 1)), (I.Shift (n + 1)))), g_, t_)
               | (I.Dot (_, s), I.Decl (g_, I.NDec _), t_)
                   -> substToSpine' (s, g_, t_)
               | (I.Dot (I.Exp u_, s), I.Decl (g_, v_), t_)
                   -> substToSpine' (s, g_, (I.App (u_, t_)))
               | (I.Dot (I.Idx n, s), I.Decl (g_, I.Dec (_, v_)), t_)
                   -> let (us_, _) =
                        Whnf.whnfEta
                        (((I.Root ((I.BVar n), I.nil_)), I.id), (v_, I.id))
                        in substToSpine' (s, g_, (I.App ((I.EClo us_), t_)))
               | (I.Dot (_, s), I.Decl (g_, I.BDec (_, (l_, t))), t_)
                   -> substToSpine' (s, g_, t_)(* Attempted fix, didn't work because I don't know how you
             computed splitting candidates for Blocks
             --cs Sat Jan  4 22:38:01 2003
          *)(* Treat like I.NDec *)(* was: I.Idx in previous line, Sun Jan  5 11:02:19 2003 -fp *)(* Eta-expand *)(* Unusable meta-decs are eliminated here *)(* Skip over NDec's; must be either Undef or Idx [from eta-expansion] *);;
    (* I.Axp, I.Block(B) or other I.Undef impossible *);;
    (* substToSpine (s, G) = S
       If   G' |- s : G
       then G' |- S : {{G}} type

       Note: {{G}} erases void declarations in G
     *);;
    let rec substToSpine (s, g_) = substToSpine' (s, g_, I.nil_);;
    (* purify' G = (G', s) where all NDec's have been erased from G
       If    |- G ctx
       then  |- G ctx and  G' |- s : G
    *);;
    let rec purify' =
      function 
               | null_ -> (I.null_, I.id)
               | I.Decl (g_, I.NDec _)
                   -> let (g'_, s) = purify' g_
                        in (g'_, (I.Dot (I.undef_, s)))
                        (* G' |- s : G *)(* G' |- _.s : G,_ *)
               | I.Decl (g_, (I.Dec _ as d_))
                   -> let (g'_, s) = purify' g_
                        in ((I.Decl (g'_, I.decSub (d_, s))), I.dot1 s)
                        (* G' |- s : G *)(* G |- D : type *)(* G' |- D[s] : type *)(* G', D[s] |- 1 : D[s][^] *)(* G', D[s] |- s o ^ : G *)(* G', D[s] |- 1.s o ^ : G, D *)
               | I.Decl (g_, (I.BDec _ as d_))
                   -> let (g'_, s) = purify' g_
                        in (g'_, (I.Dot (I.undef_, s)))
                        (* G' |- s : G *)(* G' |- _.s : G,_ *)(* added a new case to throw out blocks
         -cs Sat Jan  4 22:55:12 2003
      *);;
    (* purify G = G' where all NDec's have been erased from G
       If   |- G ctx
       then |- G' ctx
    *);;
    let rec purify g_ = (fun (r, _) -> r) (purify' g_);;
    (* coverageCheckCases (W, Cs, G) = R

       Invariant:
       If   Cs = [(G1, s1) .... (Gn, sn)]
       and  Gi |- si : G
       and  for all worlds Phi
       and  instantiations Phi |- s : G
       there exists at least one index k and substitution   Phi |- t : Gk
       s.t.  sk o t = s
    *);;
    let rec coverageCheckCases (w, cs_, g_) =
      let _ = chatter 4 (function 
                                  | () -> "[Tomega coverage checker...")
        in let _ = chatter 4 (function 
                                       | () -> "\n")
             in let ccs =
                  List.map
                  (function 
                            | (gi_, si)
                                -> (CClause (gi_, substToSpine (si, g_))))
                  cs_
                  in let _ =
                       chatter
                       6
                       (function 
                                 | () -> "[Begin covering clauses]\n")
                       in let _ =
                            List.app
                            (function 
                                      | cc
                                          -> chatter
                                             6
                                             (function 
                                                       | ()
                                                           -> (showCClause cc)
                                                                ^ "\n"))
                            ccs
                            in let _ =
                                 chatter
                                 6
                                 (function 
                                           | () -> "[End covering clauses]\n")
                                 in let pureG = purify g_
                                      in let namedG = N.ctxLUName pureG
                                           in let r0_ =
                                                substToSpine (I.id, namedG)
                                                in let cg0 =
                                                     (CGoal (namedG, r0_))
                                                     in let missing =
                                                          cover
                                                          (cg0, w, ccs, Top,
                                                           [])
                                                          in let _ =
                                                               begin
                                                               match missing
                                                               with 
                                                                    | 
                                                                    [] -> ()
                                                                    | 
                                                                    (_ :: _)
                                                                    -> 
                                                                    raise
                                                                    ((Error
                                                                    "Coverage error"))
                                                               end
                                                               (* all cases covered *)
                                                               in let _ =
                                                                    chatter
                                                                    4
                                                                    (function 
                                                                    | ()
                                                                    -> "]\n")
                                                                    in ()
                                                                    (* Question: are all the Gi's above named already? *);;
    end;;
(* functor Cover *);;