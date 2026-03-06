open! Basis;;
(* Mode Checking *);;
(* Author: Carsten Schuermann *);;
(* Modified: Frank Pfenning, Roberto Virga *);;
module ModeCheck(ModeCheck__0: sig
                               (*! structure IntSyn : INTSYN !*)
                               module ModeTable : MODETABLE
                               (*! sharing ModeSyn.IntSyn = IntSyn !*)
                               module Whnf : WHNF
                               (*! sharing Whnf.IntSyn = IntSyn !*)
                               module Index : INDEX
                               (*! sharing Index.IntSyn = IntSyn !*)
                               (*! structure Paths : PATHS !*)
                               module Origins : ORIGINS
                               end) : MODECHECK
  =
  struct
    (*! structure IntSyn = IntSyn !*);;
    (*! structure ModeSyn = ModeSyn !*);;
    (*! structure Paths = Paths !*);;
    exception Error of string ;;
    open!
      struct
        module I = IntSyn;;
        module M = ModeSyn;;
        module P = Paths;;
        type uniqueness_ = | Unique 
                           | Ambig ;;
        type info_ = | Free 
                     | Unknown 
                     | Ground of uniqueness_ ;;
        type status_ = | Existential of info_ * string option 
                       | Universal ;;
        let checkFree = ref false;;
        let rec wrapMsg (c, occ, msg) =
          begin
          match Origins.originLookup c
          with 
               | (fileName, None) -> (fileName ^ ":") ^ msg
               | (fileName, Some occDec)
                   -> P.wrapLoc'
                      ((P.Loc (fileName, P.occToRegionClause occDec occ)),
                       Origins.linesInfoLookup fileName,
                       (("Constant " ^ (Names.qidToString (Names.constQid c)))
                          ^ "\n")
                         ^ msg)
          end;;
        let rec wrapMsg' (fileName, r, msg) =
          P.wrapLoc ((P.Loc (fileName, r)), msg);;
        exception ModeError of P.occ * string ;;
        exception Error' of P.occ * string ;;
        let rec lookup (a, occ) =
          begin
          match ModeTable.mmodeLookup a
          with 
               | []
                   -> raise
                      ((Error'
                        (occ,
                         "No mode declaration for " ^
                           (I.conDecName (I.sgnLookup a)))))
               | sMs -> sMs
          end;;
        let rec nameOf =
          function 
                   | Existential (_, None) -> "?"
                   | Existential (_, Some name) -> name
                   | _ -> "?";;
        let rec unique =
          function 
                   | (k, []) -> true
                   | (k, (k' :: ks)) -> (k <> k') && (unique (k, ks));;
        let rec isUniversal = function 
                                       | Universal -> true
                                       | _ -> false;;
        let rec isGround =
          function 
                   | Existential (Ground _, _) -> true
                   | _ -> false;;
        let rec uniqueness =
          function 
                   | Existential (Ground u, _) -> u
                   | Universal -> Unique;;
        let rec ambiguate =
          function 
                   | plus_ -> M.plus_
                   | minus_ -> M.minus_
                   | minus1_ -> M.minus_;;
        let rec andUnique = function 
                                     | (Unique, Unique) -> Unique
                                     | _ -> Ambig;;
        let rec isFree = function 
                                  | Existential (Free, _) -> true
                                  | _ -> false;;
        exception Eta ;;
        let rec etaContract =
          function 
                   | (I.Root (I.BVar k, s_), n) -> begin
                       if k > n then begin
                                       etaSpine (s_, n);k - n
                                       end
                       else raise Eta end
                   | (I.Lam (d_, u_), n) -> etaContract (u_, n + 1)
                   | _ -> raise Eta
        and etaSpine =
          function 
                   | (nil_, 0) -> ()
                   | (I.App (u_, s_), n) -> begin
                       if (etaContract (u_, 0)) = n then etaSpine (s_, n - 1)
                       else raise Eta end;;
        let rec checkPattern =
          function 
                   | (d_, k, args, nil_) -> ()
                   | (d_, k, args, I.App (u_, s_))
                       -> let k' = etaContract (u_, 0) in begin
                            if
                            (k > k') &&
                              ((isUniversal (I.ctxLookup (d_, k'))) &&
                                 (unique (k', args)))
                            then checkPattern (d_, k, (k' :: args), s_) else
                            raise Eta end;;
        let rec isPattern (d_, k, s_) =
          try begin
                checkPattern (d_, k, [], s_);true
                end with 
                         | Eta -> false;;
        let rec strictExpN =
          function 
                   | (d_, _, I.Uni _) -> false
                   | (d_, p, I.Lam (_, u_))
                       -> strictExpN ((I.Decl (d_, Universal)), p + 1, u_)
                   | (d_, p, I.Pi ((d'_, _), u_))
                       -> (strictDecN (d_, p, d'_)) ||
                            (strictExpN ((I.Decl (d_, Universal)), p + 1, u_))
                   | (d_, p, I.Root (h_, s_))
                       -> begin
                          match h_
                          with 
                               | I.BVar k' -> begin
                                   if k' = p then isPattern (d_, k', s_) else
                                   begin
                                   if isUniversal (I.ctxLookup (d_, k')) then
                                   strictSpineN (d_, p, s_) else false end
                                   end
                               | I.Const c -> strictSpineN (d_, p, s_)
                               | I.Def d -> strictSpineN (d_, p, s_)
                               | I.FgnConst (cs, conDec)
                                   -> strictSpineN (d_, p, s_)
                          end
                   | (d_, p, I.FgnExp (cs, ops)) -> false
        and strictSpineN =
          function 
                   | (_, _, nil_) -> false
                   | (d_, p, I.App (u_, s_))
                       -> (strictExpN (d_, p, u_)) ||
                            (strictSpineN (d_, p, s_))
        and strictDecN (d_, p, I.Dec (_, v_)) = strictExpN (d_, p, v_);;
        let rec freeExpN =
          function 
                   | (d_, d, mode, I.Root (I.BVar k, s_), occ, strictFun)
                       -> begin
                            freeVar (d_, d, mode, k, P.head occ, strictFun);
                            freeSpineN (d_, d, mode, s_, (1, occ), strictFun)
                            end
                   | (d_, d, mode, I.Root (I.Const _, s_), occ, strictFun)
                       -> freeSpineN (d_, d, mode, s_, (1, occ), strictFun)
                   | (d_, d, mode, I.Root (I.Def _, s_), occ, strictFun)
                       -> freeSpineN (d_, d, mode, s_, (1, occ), strictFun)
                   | (d_, d, mode, I.Root (I.FgnConst (cs, conDec), s_), occ,
                      strictFun)
                       -> freeSpineN (d_, d, mode, s_, (1, occ), strictFun)
                   | (d_, d, mode, I.Lam (_, u_), occ, strictFun)
                       -> freeExpN
                          ((I.Decl (d_, Universal)), d + 1, mode, u_,
                           P.body occ, strictFun)
                   | (d_, d, mode, I.FgnExp csfe, occ, strictFun)
                       -> I.FgnExpStd.App.apply
                          csfe
                          (function 
                                    | u_
                                        -> freeExpN
                                           (d_, d, mode,
                                            Whnf.normalize (u_, I.id), occ,
                                            strictFun))
        and freeSpineN =
          function 
                   | (d_, d, mode, nil_, _, strictFun) -> ()
                   | (d_, d, mode, I.App (u_, s_), (p, occ), strictFun)
                       -> begin
                            freeExpN
                            (d_, d, mode, u_, P.arg (p, occ), strictFun);
                            freeSpineN
                            (d_, d, mode, s_, (p + 1, occ), strictFun)
                            end
        and freeVar (d_, d, mode, k, occ, strictFun) =
          let status = I.ctxLookup (d_, k) in begin
            if
            (isFree status) || ((isUniversal status) || (strictFun (k - d)))
            then () else
            raise
            ((ModeError
              (occ,
               ((("Occurrence of variable " ^ (nameOf status)) ^ " in ") ^
                  (M.modeToString mode))
                 ^ " argument not free")))
            end;;
        let rec nonStrictExpN =
          function 
                   | (d_, I.Root (I.BVar k, s_))
                       -> nonStrictSpineN (nonStrictVarD (d_, k), s_)
                   | (d_, I.Root (I.Const c, s_)) -> nonStrictSpineN (d_, s_)
                   | (d_, I.Root (I.Def d, s_)) -> nonStrictSpineN (d_, s_)
                   | (d_, I.Root (I.FgnConst (cs, conDec), s_))
                       -> nonStrictSpineN (d_, s_)
                   | (d_, I.Lam (_, u_))
                       -> I.ctxPop
                          (nonStrictExpN ((I.Decl (d_, Universal)), u_))
                   | (d_, I.FgnExp _)
                       -> raise
                          ((Error
                            "Foreign expressions not permitted when checking freeness"))
        and nonStrictSpineN =
          function 
                   | (d_, nil_) -> d_
                   | (d_, I.App (u_, s_))
                       -> nonStrictSpineN (nonStrictExpN (d_, u_), s_)
        and nonStrictVarD =
          function 
                   | (I.Decl (d_, Existential (Free, name)), 1)
                       -> (I.Decl (d_, (Existential (Unknown, name))))
                   | (d_, 1) -> d_
                   | (I.Decl (d_, status), k)
                       -> (I.Decl (nonStrictVarD (d_, k - 1), status));;
        let rec updateExpN =
          function 
                   | (d_, I.Root (I.BVar k, s_), u) -> begin
                       if isUniversal (I.ctxLookup (d_, k)) then
                       updateSpineN (d_, s_, u) else begin
                       if isPattern (d_, k, s_) then updateVarD (d_, k, u)
                       else begin
                       if ! checkFree then
                       nonStrictSpineN (nonStrictVarD (d_, k), s_) else d_
                       end end end
                   | (d_, I.Root (I.Const c, s_), u)
                       -> updateSpineN (d_, s_, u)
                   | (d_, I.Root (I.Def d, s_), u)
                       -> updateSpineN (d_, s_, u)
                   | (d_, I.Root (I.FgnConst (cs, conDec), s_), u)
                       -> updateSpineN (d_, s_, u)
                   | (d_, I.Lam (_, u_), u)
                       -> I.ctxPop
                          (updateExpN ((I.Decl (d_, Universal)), u_, u))
                   | (d_, I.FgnExp _, u) -> d_
        and updateSpineN =
          function 
                   | (d_, nil_, u) -> d_
                   | (d_, I.App (u_, s_), u)
                       -> updateSpineN (updateExpN (d_, u_, u), s_, u)
        and updateVarD =
          function 
                   | (I.Decl (d_, Existential (_, name)), 1, u)
                       -> (I.Decl (d_, (Existential ((Ground u), name))))
                   | (I.Decl (d_, status), k, u)
                       -> (I.Decl (updateVarD (d_, k - 1, u), status));;
        let rec updateAtom' =
          function 
                   | (d_, mode, nil_, mnil_, _) -> d_
                   | (d_, plus_, I.App (u_, s_), M.Mapp
                      (M.Marg (plus_, _), mS), (p, occ))
                       -> updateAtom'
                          (updateExpN (d_, u_, Unique), M.plus_, s_, mS,
                           (p + 1, occ))
                   | (d_, minus_, I.App (u_, s_), M.Mapp
                      (M.Marg (minus_, _), mS), (p, occ))
                       -> updateAtom'
                          (updateExpN (d_, u_, Ambig), M.minus_, s_, mS,
                           (p + 1, occ))
                   | (d_, minus_, I.App (u_, s_), M.Mapp
                      (M.Marg (minus1_, _), mS), (p, occ))
                       -> updateAtom'
                          (updateExpN (d_, u_, Ambig), M.minus_, s_, mS,
                           (p + 1, occ))
                   | (d_, minus1_, I.App (u_, s_), M.Mapp
                      (M.Marg (minus_, _), mS), (p, occ))
                       -> updateAtom'
                          (updateExpN (d_, u_, Ambig), M.minus1_, s_, mS,
                           (p + 1, occ))
                   | (d_, minus1_, I.App (u_, s_), M.Mapp
                      (M.Marg (minus1_, _), mS), (p, occ))
                       -> updateAtom'
                          (updateExpN (d_, u_, Unique), M.minus1_, s_, mS,
                           (p + 1, occ))
                   | (d_, mode, I.App (u_, s_), M.Mapp (_, mS), (p, occ))
                       -> updateAtom' (d_, mode, s_, mS, (p + 1, occ));;
        let rec freeAtom =
          function 
                   | (d_, mode, nil_, vs_, mnil_, _) -> ()
                   | (d_, minus_, I.App (u_, s_),
                      (I.Pi ((I.Dec (_, v1_), _), v2_), s), M.Mapp
                      (M.Marg (minus_, _), mS), (p, occ))
                       -> begin
                            freeExpN
                            (d_, 0, M.minus_, u_, P.arg (p, occ),
                             function 
                                      | q
                                          -> strictExpN
                                             (d_, q, Whnf.normalize (v1_, s)));
                            freeAtom
                            (d_, M.minus_, s_,
                             Whnf.whnfExpandDef
                             (v2_, (I.Dot ((I.Exp u_), s))), mS,
                             (p + 1, occ))
                            
                            end
                   | (d_, mode, I.App (u_, s_), (I.Pi (_, v2_), s), M.Mapp
                      (_, mS), (p, occ))
                       -> freeAtom
                          (d_, mode, s_,
                           Whnf.whnfExpandDef (v2_, (I.Dot ((I.Exp u_), s))),
                           mS, (p + 1, occ));;
        let rec updateAtom (d_, mode, s_, a, mS, (p, occ)) =
          let _ = begin
            if ! checkFree then
            freeAtom
            (d_, ambiguate mode, s_, (I.constType a, I.id), mS, (p, occ))
            else () end in updateAtom' (d_, mode, s_, mS, (p, occ));;
        let rec groundExpN =
          function 
                   | (d_, mode, I.Root (I.BVar k, s_), occ)
                       -> andUnique
                          (groundVar (d_, mode, k, P.head occ),
                           groundSpineN (d_, mode, s_, (1, occ)))
                   | (d_, mode, I.Root (I.Const c, s_), occ)
                       -> groundSpineN (d_, mode, s_, (1, occ))
                   | (d_, mode, I.Root (I.Def d, s_), occ)
                       -> groundSpineN (d_, mode, s_, (1, occ))
                   | (d_, mode, I.Root (I.FgnConst (cs, conDec), s_), occ)
                       -> groundSpineN (d_, mode, s_, (1, occ))
                   | (d_, mode, I.Lam (_, u_), occ)
                       -> groundExpN
                          ((I.Decl (d_, Universal)), mode, u_, P.body occ)
                   | (d_, mode, I.FgnExp csfe, occ)
                       -> I.FgnExpStd.fold
                          csfe
                          (function 
                                    | (u_, u)
                                        -> andUnique
                                           (groundExpN
                                            (d_, mode,
                                             Whnf.normalize (u_, I.id), occ),
                                            u))
                          Unique
        and groundSpineN =
          function 
                   | (d_, mode, nil_, _) -> Unique
                   | (d_, mode, I.App (u_, s_), (p, occ))
                       -> andUnique
                          (groundExpN (d_, mode, u_, P.arg (p, occ)),
                           groundSpineN (d_, mode, s_, (p + 1, occ)))
        and groundVar =
          function 
                   | (d_, minus1_, k, occ)
                       -> begin
                          match I.ctxLookup (d_, k)
                          with 
                               | Existential (Ground Unique, _) -> Unique
                               | Universal -> Unique
                               | (Existential (Ground Ambig, x) as s)
                                   -> raise
                                      ((ModeError
                                        (occ,
                                         ((("Occurrence of variable " ^
                                              (nameOf s))
                                             ^ " in ")
                                            ^ (M.modeToString M.minus1_))
                                           ^
                                           " argument not necessarily unique")))
                               | s
                                   -> raise
                                      ((ModeError
                                        (occ,
                                         ((("Occurrence of variable " ^
                                              (nameOf s))
                                             ^ " in ")
                                            ^ (M.modeToString M.minus1_))
                                           ^
                                           " argument not necessarily ground")))
                          end
                   | (d_, mode, k, occ)
                       -> let status = I.ctxLookup (d_, k) in begin
                            if (isGround status) || (isUniversal status) then
                            uniqueness status else
                            raise
                            ((ModeError
                              (occ,
                               ((("Occurrence of variable " ^ (nameOf status))
                                   ^ " in ")
                                  ^ (M.modeToString mode))
                                 ^ " argument not necessarily ground")))
                            end;;
        let rec groundAtom =
          function 
                   | (d_, _, nil_, mnil_, _) -> Unique
                   | (d_, plus_, I.App (u_, s_), M.Mapp
                      (M.Marg (plus_, _), mS), (p, occ))
                       -> andUnique
                          (groundExpN (d_, M.plus_, u_, P.arg (p, occ)),
                           groundAtom (d_, M.plus_, s_, mS, (p + 1, occ)))
                   | (d_, minus_, I.App (u_, s_), M.Mapp
                      (M.Marg (minus_, _), mS), (p, occ))
                       -> begin
                            groundExpN (d_, M.minus_, u_, P.arg (p, occ));
                            groundAtom (d_, M.minus_, s_, mS, (p + 1, occ))
                            end
                   | (d_, minus_, I.App (u_, s_), M.Mapp
                      (M.Marg (minus1_, _), mS), (p, occ))
                       -> begin
                            groundExpN (d_, M.minus1_, u_, P.arg (p, occ));
                            groundAtom (d_, M.minus_, s_, mS, (p + 1, occ))
                            end
                   | (d_, mode, I.App (u_, s_), M.Mapp (_, mS), (p, occ))
                       -> groundAtom (d_, mode, s_, mS, (p + 1, occ));;
        let rec ctxPush (m, ds_) =
          List.map (function 
                             | d_ -> (I.Decl (d_, m))) ds_;;
        let rec ctxPop ds_ = List.map (function 
                                                | I.Decl (d_, m) -> d_) ds_;;
        let rec checkD1 =
          function 
                   | (d_, I.Pi ((I.Dec (name, _), maybe_), v_), occ, k)
                       -> checkD1
                          ((I.Decl (d_, (Existential (Free, name)))), v_,
                           P.body occ,
                           function 
                                    | I.Decl (d'_, m) -> ctxPush (m, k d'_))
                   | (d_, I.Pi ((I.Dec (name, v1_), no_), v2_), occ, k)
                       -> checkD1
                          ((I.Decl (d_, (Existential (Free, name)))), v2_,
                           P.body occ,
                           function 
                                    | I.Decl (d'_, m)
                                        -> ctxPush
                                           (m,
                                            checkG1
                                            (d'_, v1_, P.label occ, k)))
                   | (d_, I.Root (I.Const a, s_), occ, k)
                       -> let rec checkAll =
                            function 
                                     | [] -> ()
                                     | (mS :: mSs)
                                         -> let rec checkSome =
                                              function 
                                                       | (d'_ :: [])
                                                           -> begin
                                                                groundAtom
                                                                (d'_,
                                                                 M.minus_,
                                                                 s_, mS,
                                                                 (1, occ));
                                                                checkAll mSs
                                                                end
                                                       | (d'_ :: ds_)
                                                           -> begin
                                                                try begin
                                                                    groundAtom
                                                                    (d'_,
                                                                    M.minus_,
                                                                    s_, mS,
                                                                    (1, occ));
                                                                    ()
                                                                    end
                                                                with 
                                                                
                                                                | ModeError _
                                                                    -> 
                                                                    checkSome
                                                                    ds_;
                                                                checkAll mSs
                                                                end
                                              in checkSome
                                                 (k
                                                  (updateAtom
                                                   (d_, M.plus_, s_, a, mS,
                                                    (1, occ))))
                            in checkAll (lookup (a, occ))
                   | (d_, I.Root (I.Def d, s_), occ, k)
                       -> let rec checkAll =
                            function 
                                     | [] -> ()
                                     | (mS :: mSs)
                                         -> let rec checkSome =
                                              function 
                                                       | (d'_ :: [])
                                                           -> begin
                                                                groundAtom
                                                                (d'_,
                                                                 M.minus_,
                                                                 s_, mS,
                                                                 (1, occ));
                                                                checkAll mSs
                                                                end
                                                       | (d'_ :: ds_)
                                                           -> begin
                                                                try begin
                                                                    groundAtom
                                                                    (d'_,
                                                                    M.minus_,
                                                                    s_, mS,
                                                                    (1, occ));
                                                                    ()
                                                                    end
                                                                with 
                                                                
                                                                | ModeError _
                                                                    -> 
                                                                    checkSome
                                                                    ds_;
                                                                checkAll mSs
                                                                end
                                              in checkSome
                                                 (k
                                                  (updateAtom
                                                   (d_, M.plus_, s_, d, mS,
                                                    (1, occ))))
                            in checkAll (lookup (d, occ))
        and checkG1 =
          function 
                   | (d_, I.Pi ((_, maybe_), v_), occ, k)
                       -> ctxPop
                          (checkG1
                           ((I.Decl (d_, Universal)), v_, P.body occ,
                            function 
                                     | I.Decl (d'_, m) -> ctxPush (m, k d'_)))
                   | (d_, I.Pi ((I.Dec (_, v1_), no_), v2_), occ, k)
                       -> ctxPop
                          (begin
                             checkD1
                             (d_, v1_, P.label occ, function 
                                                             | d'_ -> [d'_]);
                             checkG1
                             ((I.Decl (d_, Universal)), v2_, P.body occ,
                              function 
                                       | I.Decl (d'_, m)
                                           -> ctxPush (m, k d'_))
                             
                             end)
                   | (d_, I.Root (I.Const a, s_), occ, k)
                       -> let rec checkList arg__1 arg__2 =
                            begin
                            match (arg__1, arg__2)
                            with 
                                 | (found, []) -> []
                                 | (false, (mS :: []))
                                     -> begin
                                        match groundAtom
                                              (d_, M.plus_, s_, mS, (1, occ))
                                        with 
                                             | Unique
                                                 -> k
                                                    (updateAtom
                                                     (d_, M.minus1_, s_, a,
                                                      mS, (1, occ)))
                                             | Ambig
                                                 -> k
                                                    (updateAtom
                                                     (d_, M.minus_, s_, a,
                                                      mS, (1, occ)))
                                        end
                                 | (found, (mS :: mSs))
                                     -> let found' =
                                          try begin
                                                groundAtom
                                                (d_, M.plus_, s_, mS,
                                                 (1, occ));
                                                true
                                                end
                                          with 
                                               | ModeError _ -> false
                                          in let ds'_ =
                                               checkList
                                               (found || found')
                                               mSs in begin
                                               if found' then
                                               (k
                                                (updateAtom
                                                 (d_, M.minus_, s_, a, mS,
                                                  (1, occ))))
                                                 @ ds'_
                                               else ds'_ end
                            end in checkList false (lookup (a, occ))
                   | (d_, I.Root (I.Def d, s_), occ, k)
                       -> let rec checkList arg__3 arg__4 =
                            begin
                            match (arg__3, arg__4)
                            with 
                                 | (found, []) -> []
                                 | (false, (mS :: []))
                                     -> begin
                                        match groundAtom
                                              (d_, M.plus_, s_, mS, (1, occ))
                                        with 
                                             | Unique
                                                 -> k
                                                    (updateAtom
                                                     (d_, M.minus1_, s_, d,
                                                      mS, (1, occ)))
                                             | Ambig
                                                 -> k
                                                    (updateAtom
                                                     (d_, M.minus_, s_, d,
                                                      mS, (1, occ)))
                                        end
                                 | (found, (mS :: mSs))
                                     -> let found' =
                                          try begin
                                                groundAtom
                                                (d_, M.plus_, s_, mS,
                                                 (1, occ));
                                                true
                                                end
                                          with 
                                               | ModeError _ -> false
                                          in let ds'_ =
                                               checkList
                                               (found || found')
                                               mSs in begin
                                               if found' then
                                               (k
                                                (updateAtom
                                                 (d_, M.minus_, s_, d, mS,
                                                  (1, occ))))
                                                 @ ds'_
                                               else ds'_ end
                            end in checkList false (lookup (d, occ));;
        let rec checkDlocal (d_, v_, occ) =
          try checkD1 (d_, v_, occ, function 
                                             | d'_ -> [d'_])
          with 
               | ModeError (occ, msg) -> raise ((Error' (occ, msg)));;
        let rec cidFromHead = function 
                                       | I.Const a -> a
                                       | I.Def a -> a;;
        let rec checkD (conDec, fileName, occOpt) =
          let _ = checkFree := false
            in let rec checkable =
                 function 
                          | I.Root (ha_, _)
                              -> begin
                                 match ModeTable.mmodeLookup
                                       (cidFromHead ha_)
                                 with 
                                      | [] -> false
                                      | _ -> true
                                 end
                          | I.Uni _ -> false
                          | I.Pi (_, v_) -> checkable v_
                 in let v_ = I.conDecType conDec in begin
                      if checkable v_ then
                      try checkDlocal (I.null_, v_, P.top)
                      with 
                           | Error' (occ, msg)
                               -> begin
                                  match occOpt
                                  with 
                                       | None -> raise ((Error msg))
                                       | Some occTree
                                           -> raise
                                              ((Error
                                                (wrapMsg'
                                                 (fileName,
                                                  P.occToRegionClause
                                                  occTree
                                                  occ, msg))))
                                  end
                      else () end;;
        let rec checkAll =
          function 
                   | [] -> ()
                   | (I.Const c :: clist)
                       -> begin
                            begin
                            if (! Global.chatter) > 3 then
                            print
                            ((Names.qidToString (Names.constQid c)) ^ " ")
                            else () end;
                            begin
                              try checkDlocal (I.null_, I.constType c, P.top)
                              with 
                                   | Error' (occ, msg)
                                       -> raise
                                          ((Error (wrapMsg (c, occ, msg))));
                              checkAll clist
                              end
                            
                            end
                   | (I.Def d :: clist)
                       -> begin
                            begin
                            if (! Global.chatter) > 3 then
                            print
                            ((Names.qidToString (Names.constQid d)) ^ " ")
                            else () end;
                            begin
                              try checkDlocal (I.null_, I.constType d, P.top)
                              with 
                                   | Error' (occ, msg)
                                       -> raise
                                          ((Error (wrapMsg (d, occ, msg))));
                              checkAll clist
                              end
                            
                            end;;
        let rec checkMode (a, ms) =
          let _ = begin
            if (! Global.chatter) > 3 then
            print
            (("Mode checking family " ^
                (Names.qidToString (Names.constQid a)))
               ^ ":\n")
            else () end
            in let clist = Index.lookup a
                 in let _ = checkFree := false
                      in let _ = checkAll clist
                           in let _ = begin
                                if (! Global.chatter) > 3 then print "\n"
                                else () end in ();;
        let rec checkFreeOut (a, ms) =
          let _ = begin
            if (! Global.chatter) > 3 then
            print
            (("Checking output freeness of " ^
                (Names.qidToString (Names.constQid a)))
               ^ ":\n")
            else () end
            in let clist = Index.lookup a
                 in let _ = checkFree := true
                      in let _ = checkAll clist
                           in let _ = begin
                                if (! Global.chatter) > 3 then print "\n"
                                else () end in ();;
        end;;
    (* Uniqueness information *);;
    (* u ::= Unique           *);;
    (*     | Ambig            *);;
    (* Groundedness information   *);;
    (* I ::= Free                 *);;
    (*     | Unknown              *);;
    (*     | Ground               *);;
    (* Variable status             *);;
    (* S ::= Existential (I, xOpt) *);;
    (*     | Universal             *);;
    (* hack: if true, check freeness of output arguments in subgoals *);;
    (* Representation invariant:

       Groundness information:
       T stands for ground, B stands for unknown
       Ex  for a named existential variable
       Par for a parameter

       Mode context   D ::= . | D, S

       If D contains Status information for variables in
       a context G, we write G ~ D
       We write D' >= D if for all i
         D(i) par iff D'(i) par
         D(i) bot implies D'(i) bot or D'(i) top
         D(i) top implies D'(i) top
    *);;
    (* copied from worldcheck/worldsyn.fun *);;
    (* lookup (a, occ) = mSs

       Invariant: mS are the argument modes for a
       Raises an error if no mode for a has declared.
       (occ is used in error message)
    *);;
    (* nameOf S, selects a name for S *);;
    (* unique (k, ks) = B

       Invariant:
       B iff k does not occur in ks
    *);;
    (* isUniversal S = B

       Invariant:
       B iff S = Par
    *);;
    (* isGround S = B

       Invariant:
       B iff S = Ex (T x)
    *);;
    (* uniqueness S = u
       where u is the uniqueness property of status S
    *);;
    (* ambiguate (mode) = mode'
       where mode' forgets uniqueness properties
    *);;
    (* andUnique (u1, u2) = Unique if u1 = u2 = Unique
       = Ambig otherwise
    *);;
    (* isFree S = b

       Invariant:
       b iff S = Ex (B x)
    *);;
    (* etaContract (U, n) = k

       if lam V1... lam Vn. U =eta*=> k
       otherwise raise exception Eta

       Invariant: G, V1,..., Vn |- U : V for some G, Vi, V.
                  U in NF
    *);;
    (* etaSpine (S, n) = ()
       if S =eta*=> n ; n-1 ; ... ; 1 ; Nil
       otherwise raise exception Eta

       Invariant: G |- S : V1 >> V2 for some G, V1, V2
                  S in NF
    *);;
    (* S[s] should be impossible *);;
    (* isPattern (D, k, mS) = B

       Invariant:
       B iff k > k' for all k' in mS
         and for all k in mS: k is parameter
         and for all k', k'' in mS: k' <> k''
    *);;
    (* ------------------------------------------- strictness check *);;
    (* This repeats some code from ../typecheck/strict.fun *);;
    (* Interface here is somewhat different *);;
    (* strictExpN (D, p, U) = B

       Invariant:
       If  D |- U : V
       and U is in nf (normal form)
       then B iff U is strict in p
    *);;
    (* checking D in this case should be redundant -fp *);;
    (* strictDecN (D, p, D) orelse *);;
    (* equivalently: isUniversal .. andalso strictSpineN .. *);;
    (* no other cases possible *);;
    (* this is a hack - until we investigate this further   -rv *);;
    (* no other cases possible *);;
    (* strictSpineN (D, S) = B

       Invariant:
       If  D |- S : V > W
       and S is in nf (normal form)
       then B iff S is strict in k
    *);;
    (*
    fun strictAtom (D, p, mode, I.Nil, (V, s), M.Mnil) = false
      | strictAtom (D, p, M.Minus, I.App (U, S), (I.Pi ((I.Dec (_, V1), _), V2), s),
                     M.Mapp (M.Marg (M.Minus, _), mS)) =
          strictExpN (D, p, Whnf.normalize (V1, s))
          orelse strictAtom (D, p, M.Minus, S, Whnf.whnfExpandDef (V2, I.Dot (I.Exp U, s)), mS)
      | strictAtom (D, p, mode, I.App (U, S), (I.Pi (_, V2), s), M.Mapp(_, mS)) =
          strictAtom (D, p, mode, S, Whnf.whnfExpandDef (V2, I.Dot (I.Exp U, s)), mS)
    *);;
    (* ------------------------------------------- freeness check *);;
    (* freeExpN (D, mode, U, occ = ()

       If G |- U : V  (U in nf)
       and G ~ D
       then freeExpN terminates with () if D |- U free
       else exception ModeError is raised

       (occ and mode are used in error messages)
    *);;
    (* punting on the occ here  - ak *);;
    (* freeSpineN (D, mode, S, occ, strictFun)  = ()

       If   G |- S : V1  > V2   (S in nf)
       and  G ~ D
       then freeSpineN terminates with () if  D |- S free
       else exception ModeError is raised

       (occ and mode are used in error messages)
    *);;
    (* freeVar (D, mode, k, occ, strictFun)  = ()

       If   G |- k : V1
       and  G ~ D
       then freeVar terminates with () if  D |- S free
       else exception ModeError is raised

       (occ and mode are used in error messages)
    *);;
    (* -------------------------------- non-strict mode context update *);;
    (* nonStrictExpN (D, U) = D'

       If   G |- U : V     (U in nf)
       and  D ~ G
       then D' >= D where D'(k) Unknown for all existential variables k
            in U that are free in D
    *);;
    (* nonStrictSpineN (D, S) = D'

       If   G |- S : V1 > V2      (S in nf)
       and  D ~ G
       then D' >= D' where D'(k) Unkown for all existential variables k
            in S that are Free in D
    *);;
    (* nonStrictVarD (D, k) = D'

       If   G |- k : V
       and  D ~ G
       and  k is an existential variable
       then D' >= D where k is nonStrictd as described in  nonStrictExpN
    *);;
    (* Universal, or already Unknown or Ground - leave unchanged *);;
    (* ------------------------------------------- mode context update *);;
    (* updateExpN (D, U, u) = D'

       If   G |- U : V     (U in nf)
       and  D ~ G
       then D' >= D where D'(k) Ground for all existential variables k
            with a strict occurrence in U
            and D'(k) Unkown for all existential variable k
            with a non-strict occurrence, but no strict occurrence in U
            (if !checkFree is true)

       u is the uniqueness property for the new ground assumptions
    *);;
    (* no occurrence inside a FgnExp is considered strict *);;
    (* updateSpineN (D, S, u) = D'

       If   G |- S : V1 > V2      (S in nf)
       and  D ~ G
       then D' >= D' where D'(k) Ground for all existential variables k
            with a strict occurrence in S
    *);;
    (* updateVarD (D, k, u) = D'

       If   G |- k : V
       and  D ~ G
       and  k is an existential variable
       then D' >= D where k is updated as described in  updateExpN
    *);;
    (* ----------------------- mode context update by argument modes *);;
    (* updateAtom (D, m, S, mS, (p,occ)) = D'

       If   G |- S : V > V'   ( S = U1 ; .. ; Un)
       and  D ~ G
       and  S ~ mS            (mS = m1 , .. , mn)
       and  m mode
       then D' >= D where
            all Ui are updated if mi = m (mod uniqueness)

       The new ground variables are marked Unique
         if m = (-1) and mi = (-1) (when updating from subgoals with unique inputs)
         or m = mi = (+) (when updating from the clause head)
       Otherwise they are marked Ambig.

       (p,occ) is used in error message if freeness is to be checked
    *);;
    (* when checking freeness, all arguments must be input (+) or output (-) *);;
    (* therefore, no case for M.Mapp (M.Marg (M.Minus, _), mS) is provided here *);;
    (* freeAtom (D, m, S, (V,s), mS, (p, occ)) = ()

       checks if all output arguments in S according to mS are free.
       Invariant: G |- S : V[s] >> P for some G and P  (S in nf)
                  G ~ D
                  mode = (-) or (+); ( * ) or (-1) are excluded
    *);;
    (* updateAtom (D, m, S, a, mS, (p, occ))
       see updateAtom', and performs additional freeness check if required
    *);;
    (* ------------------------------------------- groundness check *);;
    (* groundExpN (D, mode, U, occ)  = u

       If   G |- U : V    (U in nf)
       and  G ~ D
       then if mode = (+) or (-)
            then groundExpN terminates with u if  D |- U ground
                 else exception ModeError is raised
            if mode = (-1) then D |- U ground and U unique
                           else exception ModeError is raised

       u = Unique if all known variables in U are Unique
       u = Ambig otherwise

       (occ and mode are used in error messages)
    *);;
    (* punting on occ here  - ak *);;
    (* groundSpineN (D, mode, S, occ)  = u

       If   G |- S : V1  > V2   (S in nf)
       and  G ~ D
       then if mode = (+) or (-)
            then groundSpineN terminates with u if  D |- S ground
                 else exception ModeError is raised
            if mode = (-1) then D |- S ground and S unique
                           else exception ModeError is raised

       u = Unique if all known variables in S are Unique
       u = Ambig otherwise

       (occ and mode are used in error messages)
    *);;
    (* groundVar (D, mode, k, occ)  = u

       If   G |- k : V1
       and  G ~ D
       then if mode = (+) or (-)
            then groundVar terminates with u if  D |- k ground
                 else exception ModeError is raised
            if mode = (-1) then D |- k ground and k unique
                           else exception ModeError is raised

       u = Unique if k is known to be unique, Ambig otherwise

       (occ and mode are used in error messages)
    *);;
    (* Existential (Free, _) or Existential (Unknown, _) *);;
    (* ------------------------------------------- groundness check by polarity *);;
    (* groundAtom (D, m, S, mS, (p,occ))  = u

       If   G |- S : V > V'   ( S = U1 ; .. ; Un)
       and  D ~ G
       and  S ~ mS            (mS = m1 , .. , mn)
       and  m mode = (+) or (-1)
       then groundAtom returns u if  D |- Ui ground
            for all i s.t. mi = m (mod uniqueness)
            and checks that D |- Ui unique if mi = (-1) and m = (-)
       otherwise exception ModeError is raised

       u = Unique if all mi = m (mod uniqueness) are unique,
       u = Ambig otherwise

       ((p,occ) used in error messages)
    *);;
    (* ignore uniqueness result here *);;
    (* ignore uniqueness result here *);;
    (* ------------------------------------------- mode checking first phase *);;
    (* ctxPush (Ds, m) = Ds'
       raises the contexts Ds prepending m
    *);;
    (* ctxPop Ds = Ds'
       lowers the contexts Ds
    *);;
    (* checkD1 (D, V, occ, k) = ()

       Invariant:
         if G |- V : L
         and  V does not contain Skolem constants
         and  D ~ G
         then
            for each  mode mS of the head of V
              exists  some Di s.t. all (-) evars of mS are ground
                where  D' ~ G, D' >= D is obtained by updating D
                  and  k D' = [D1, ..., Di, ..., Dn]
                  and  Di ~ G, Di >= D' is obtained by mode checking on the subgoals of V

       exception ModeError is raised if the expression does not mode check
       exception Error' is raised if the expression contains type families
       that have no mode information associated with them
       (occ used in error messages)
    *);;
    (* for a declaration, all modes must be satisfied *);;
    (* D' is the only (last) possibility; on failure, we raise ModeError *);;
    (* ignore return *);;
    (* try D', if it doesn't work, try another context in the Ds *);;
    (* ignore return *);;
    (* for a declaration, all modes must be satisfied *);;
    (* D' is the only (last) possibility; on failure, we raise ModeError *);;
    (* ignore return *);;
    (* try D', if it doesn't work, try another context in the Ds *);;
    (* ignore return *);;
    (* checkG1 (D, V, occ, k) = Ds

       Invariant:
         if G |- V : L
         and  V does not contain Skolem constants
         and  D ~ G
         then forall D' >= D that mode checks V, (k D') is a sublist of Ds
         and for each Di in Ds, Di ~ G and Di >= D'

       exception ModeError is raised if the expression does not mode check
       exception Error' is raised if the expression contains type families
       that have no mode information associated with them
       (occ used in error messages)
     *);;
    (* for a goal, at least one mode must be satisfied *);;
    (* found = true *);;
    (* mS is the last possible mode to check;
                    if the check fails, we don't catch ModeError *);;
    (* uniqueness not permitted on multiple modes right now *);;
    (* Wed Aug 20 21:52:31 2003 -fp *);;
    (* found' is true iff D satisfies mS *);;
    (* handler scope??? -fp *);;
    (* compute all other mode contexts *);;
    (* for a goal, at least one mode must be satisfied *);;
    (* found = true *);;
    (* mS is the last possible mode to check;
                    if the check fails, we don't catch ModeError *);;
    (* uniqueness not permitted on multiple modes right now *);;
    (* Wed Aug 20 21:52:31 2003 -fp *);;
    (* found' is true iff D satisfies mS *);;
    (* compute all other mode contexts *);;
    (* checkDlocal (D, V, occ) = ()

       Invariant:
       If   G |- V : L
       and  D ~ G
       then checkD terminates with ()  iff V is mode correct.

       otherwise exception ModeError is raised (occ used in error messages)
    *);;
    (* --------------------------------------------------------- mode checking *);;
    (* checkD (ConDec, occOpt)  = ()

       checkD terminates with () if ConDec is mode correct
       otherwise exception Error is raised

       (occOpt is used in error messages)
    *);;
    let checkD = checkD;;
    let checkMode = checkMode;;
    let checkFreeOut = checkFreeOut;;
    end;;
(*! sharing Origins.Paths = Paths !*);;
(*! sharing Origins.IntSyn = IntSyn !*);;
(* functor ModeCheck *);;