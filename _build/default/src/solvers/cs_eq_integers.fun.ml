open! Basis;;
module CSEqIntegers(CSEqIntegers__0: sig
                                     (* Diophantine Equation Solver *)
                                     (* Author: Roberto Virga *)
                                     module Integers : INTEGERS
                                     (*! structure IntSyn : INTSYN !*)
                                     module Whnf : WHNF
                                     (*! sharing Whnf.IntSyn = IntSyn !*)
                                     module Unify : UNIFY
                                     end) : CS_EQ_INTEGERS
  =
  struct
    (*! structure CSManager = CSManager !*);;
    module Integers = Integers;;
    (*! structure IntSyn = IntSyn !*);;
    type nonrec 'a mset = 'a list;;
    (* MultiSet                   *);;
    type sum_ = | Sum of Integers.int * mon_ mset 
    and mon_ = | Mon of Integers.int * (IntSyn.exp_ * IntSyn.sub_) mset ;;
    (* Sum :                      *);;
    (* Sum ::= m + M1 + ...       *);;
    (* Monomials:                 *);;
    (* Mon ::= n * U1[s1] * ...   *);;
    (* A monomial (n * U1[s1] * U2[s2] * ...) is said to be normal iff
       (a) the coefficient n is different from zero;
       (b) each (Ui,si) is in whnf and not a foreign term corresponding
           to a sum.
     A sum is normal iff all its monomials are normal, and moreover they
     are pairwise distinct.
  *);;
    open!
      struct
        open IntSyn;;
        open Integers;;
        module FX = CSManager.Fixity;;
        module MS = ModeSyn;;
        exception MyIntsynRep of sum_ ;;
        let rec extractSum =
          function 
                   | MyIntsynRep sum -> sum
                   | fe -> raise ((UnexpectedFgnExp fe));;
        let zero = fromInt 0;;
        let one = fromInt 1;;
        let myID = (ref (-1) : csid ref);;
        let numberID = (ref (-1) : cid ref);;
        let rec number () = (Root ((Const (! numberID)), Nil));;
        let unaryMinusID = (ref (-1) : cid ref);;
        let plusID = (ref (-1) : cid ref);;
        let minusID = (ref (-1) : cid ref);;
        let timesID = (ref (-1) : cid ref);;
        let rec unaryMinusExp u_ =
          (Root ((Const (! unaryMinusID)), (App (u_, Nil))));;
        let rec plusExp (u_, v_) =
          (Root ((Const (! plusID)), (App (u_, (App (v_, Nil))))));;
        let rec minusExp (u_, v_) =
          (Root ((Const (! minusID)), (App (u_, (App (v_, Nil))))));;
        let rec timesExp (u_, v_) =
          (Root ((Const (! timesID)), (App (u_, (App (v_, Nil))))));;
        let rec numberConDec d =
          (ConDec (toString d, None, 0, Normal, number (), Type));;
        let rec numberExp d =
          (Root ((FgnConst (! myID, numberConDec d)), Nil));;
        let rec parseNumber string =
          begin
          match fromString string
          with 
               | Some d -> (Some (numberConDec d))
               | None -> None
          end;;
        let rec solveNumber (g_, s_, k) = (Some (numberExp (fromInt k)));;
        let rec findMSet eq (x, l_) =
          let rec findMSet' =
            function 
                     | (tried, []) -> None
                     | (tried, (y :: l_)) -> begin
                         if eq (x, y) then (Some (y, tried @ l_)) else
                         findMSet' ((y :: tried), l_) end
            in findMSet' ([], l_);;
        let rec equalMSet eq =
          let rec equalMSet' =
            function 
                     | ([], []) -> true
                     | ((x :: l1'_), l2_)
                         -> begin
                            match findMSet eq (x, l2_)
                            with 
                                 | Some (y, l2'_) -> equalMSet' (l1'_, l2'_)
                                 | None -> false
                            end
                     | _ -> false
            in equalMSet';;
        let rec toExp =
          function 
                   | Sum (m, []) -> numberExp m
                   | Sum (m, (mon :: [])) -> begin
                       if m = zero then toExpMon mon else
                       plusExp (toExp ((Sum (m, []))), toExpMon mon) end
                   | Sum (m, ((mon :: monL) as monLL))
                       -> plusExp (toExp ((Sum (m, monL))), toExpMon mon)
        and toExpMon =
          function 
                   | Mon (n, []) -> numberExp n
                   | Mon (n, (us_ :: [])) -> begin
                       if n = one then toExpEClo us_ else
                       timesExp (toExpMon ((Mon (n, []))), toExpEClo us_) end
                   | Mon (n, (us_ :: usL_))
                       -> timesExp
                          (toExpMon ((Mon (n, usL_))), toExpEClo us_)
        and toExpEClo = function 
                                 | (u_, Shift 0) -> u_
                                 | us_ -> (EClo us_);;
        let rec compatibleMon (Mon (_, usL1_), Mon (_, usL2_)) =
          equalMSet
          (function 
                    | (us1_, us2_) -> sameExpW (us1_, us2_))
          (usL1_, usL2_)
        and sameExpW =
          function 
                   | (((Root (h1_, s1_), s1) as us1_),
                      ((Root (h2_, s2_), s2) as us2_))
                       -> begin
                          match (h1_, h2_)
                          with 
                               | (BVar k1, BVar k2)
                                   -> (k1 = k2) &&
                                        (sameSpine ((s1_, s1), (s2_, s2)))
                               | (FVar (n1, _, _), FVar (n2, _, _))
                                   -> (n1 = n2) &&
                                        (sameSpine ((s1_, s1), (s2_, s2)))
                               | _ -> false
                          end
                   | ((((EVar (r1, g1_, v1_, cnstrs1) as u1_), s1) as us1_),
                      (((EVar (r2, g2_, v2_, cnstrs2) as u2_), s2) as us2_))
                       -> (r1 = r2) && (sameSub (s1, s2))
                   | _ -> false
        and sameExp (us1_, us2_) = sameExpW (Whnf.whnf us1_, Whnf.whnf us2_)
        and sameSpine =
          function 
                   | ((Nil, s1), (Nil, s2)) -> true
                   | ((SClo (s1_, s1'), s1), ss2_)
                       -> sameSpine ((s1_, comp (s1', s1)), ss2_)
                   | (ss1_, (SClo (s2_, s2'), s2))
                       -> sameSpine (ss1_, (s2_, comp (s2', s2)))
                   | ((App (u1_, s1_), s1), (App (u2_, s2_), s2))
                       -> (sameExp ((u1_, s1), (u2_, s2))) &&
                            (sameSpine ((s1_, s1), (s2_, s2)))
                   | _ -> false
        and sameSub =
          function 
                   | (Shift _, Shift _) -> true
                   | (Dot (Idx k1, s1), Dot (Idx k2, s2))
                       -> (k1 = k2) && (sameSub (s1, s2))
                   | ((Dot (Idx _, _) as s1), Shift k2)
                       -> sameSub
                          (s1,
                           (Dot
                            ((Idx ((Int.( + ) (k2, 1)))),
                             (Shift ((Int.( + ) (k2, 1)))))))
                   | (Shift k1, (Dot (Idx _, _) as s2))
                       -> sameSub
                          ((Dot
                            ((Idx ((Int.( + ) (k1, 1)))),
                             (Shift ((Int.( + ) (k1, 1)))))),
                           s2)
                   | (_, _) -> false;;
        let rec plusSum =
          function 
                   | (Sum (m1, []), Sum (m2, monL2))
                       -> (Sum (m1 + m2, monL2))
                   | (Sum (m1, monL1), Sum (m2, []))
                       -> (Sum (m1 + m2, monL1))
                   | (Sum (m1, (mon1 :: monL1)), Sum (m2, monL2))
                       -> plusSumMon
                          (plusSum ((Sum (m1, monL1)), (Sum (m2, monL2))),
                           mon1)
        and plusSumMon =
          function 
                   | (Sum (m, []), mon) -> (Sum (m, [mon]))
                   | (Sum (m, monL), (Mon (n, usL_) as mon))
                       -> begin
                          match findMSet compatibleMon (mon, monL)
                          with 
                               | Some (Mon (n', _), monL')
                                   -> let n'' = n + n' in begin
                                        if n'' = zero then (Sum (m, monL'))
                                        else
                                        (Sum
                                         (m, ((Mon (n'', usL_)) :: monL')))
                                        end
                               | None -> (Sum (m, (mon :: monL)))
                          end;;
        let rec timesSum =
          function 
                   | (Sum (m1, []), Sum (m2, [])) -> (Sum (m1 * m2, []))
                   | (Sum (m1, (mon1 :: monL1)), sum2)
                       -> plusSum
                          (timesSumMon (sum2, mon1),
                           timesSum ((Sum (m1, monL1)), sum2))
                   | (sum1, Sum (m2, (mon2 :: monL2)))
                       -> plusSum
                          (timesSumMon (sum1, mon2),
                           timesSum (sum1, (Sum (m2, monL2))))
        and timesSumMon =
          function 
                   | (Sum (m, []), Mon (n, usL_))
                       -> let n' = m * n in begin
                            if n' = zero then (Sum (n', [])) else
                            (Sum (zero, [(Mon (n', usL_))])) end
                   | (Sum (m, (Mon (n', usL'_) :: monL)),
                      (Mon (n, usL_) as mon))
                       -> let n'' = n * n'
                            in let usL''_ = usL_ @ usL'_
                                 in let Sum (m', monL') =
                                      timesSumMon ((Sum (m, monL)), mon)
                                      in (Sum
                                          (m',
                                           ((Mon (n'', usL''_)) :: monL')));;
        let rec unaryMinusSum sum = timesSum ((Sum (- one, [])), sum);;
        let rec minusSum (sum1, sum2) = plusSum (sum1, unaryMinusSum sum2);;
        let rec fromExpW =
          function 
                   | ((FgnExp (cs, fe), _) as us_) -> begin
                       if cs = (! myID) then normalizeSum (extractSum fe)
                       else (Sum (zero, [(Mon (one, [us_]))])) end
                   | ((Root (FgnConst (cs, conDec), _), _) as us_) -> begin
                       if cs = (! myID) then
                       begin
                       match fromString (conDecName conDec)
                       with 
                            | Some m -> (Sum (m, []))
                       end else (Sum (zero, [(Mon (one, [us_]))])) end
                   | us_ -> (Sum (zero, [(Mon (one, [us_]))]))
        and fromExp us_ = fromExpW (Whnf.whnf us_)
        and normalizeSum =
          function 
                   | (Sum (m, []) as sum) -> sum
                   | Sum (m, (mon :: []))
                       -> plusSum ((Sum (m, [])), normalizeMon mon)
                   | Sum (m, (mon :: monL))
                       -> plusSum
                          (normalizeMon mon, normalizeSum ((Sum (m, monL))))
        and normalizeMon =
          function 
                   | (Mon (n, []) as mon) -> (Sum (n, []))
                   | Mon (n, (us_ :: []))
                       -> timesSum ((Sum (n, [])), fromExp us_)
                   | (Mon (n, (us_ :: usL_)) as mon)
                       -> timesSum
                          (fromExp us_, normalizeMon ((Mon (n, usL_))))
        and mapSum (f, Sum (m, monL)) =
          (Sum (m, List.map (function 
                                      | mon -> mapMon (f, mon)) monL))
        and mapMon (f, Mon (n, usL_)) =
          (Mon
           (n,
            List.map (function 
                               | us_ -> Whnf.whnf (f ((EClo us_)), id)) usL_));;
        let rec appSum (f, Sum (m, monL)) =
          List.app (function 
                             | mon -> appMon (f, mon)) monL
        and appMon (f, Mon (n, usL_)) =
          List.app (function 
                             | us_ -> f ((EClo us_))) usL_;;
        let rec solvableSum (Sum (m, monL)) =
          let rec gcd_list =
            function 
                     | (n1 :: []) -> n1
                     | (n1 :: (n2 :: [])) -> gcd (n1, n2)
                     | (n1 :: (n2 :: l)) -> gcd (gcd (n1, n2), gcd_list l)
            in let coeffL = List.map (function 
                                               | Mon (n, _) -> n) monL
                 in let g = gcd_list coeffL
                      in (rem (m, gcd_list coeffL)) = zero;;
        let rec findMon f (g_, Sum (m, monL)) =
          let rec findMon' =
            function 
                     | ([], monL2) -> None
                     | ((mon :: monL1), monL2)
                         -> begin
                            match f (g_, mon, (Sum (m, monL1 @ monL2)))
                            with 
                                 | (Some _ as result) -> result
                                 | None -> findMon' (monL1, (mon :: monL2))
                            end
            in findMon' (monL, []);;
        let rec divideSum (Sum (m, monL), k) =
          (let exception Err 
           in let rec divide n = begin
                if (rem (n, k)) = zero then quot (n, k) else raise Err end
                in let rec divideMon (Mon (n, usL_)) = (Mon (divide n, usL_))
                     in try (Some
                             ((Sum (divide m, List.map divideMon monL))))
                        with 
                             | Err -> None);;
        let rec delaySum (g_, sum) =
          let u_ = toFgn sum
            in let cnstr = ref ((Eqn (g_, u_, numberExp zero)))
                 in (Delay (u_, cnstr))
        and solveSum =
          function 
                   | (g_,
                      (Sum
                        (m,
                         (Mon (n, (((EVar (r, _, _, _) as x_), s) :: []))
                          :: []))
                        as sum))
                       -> begin
                       if Whnf.isPatSub s then
                       [(Assign
                         (g_, x_, numberExp (- (quot (m, n))), Whnf.invert s))]
                       else [delaySum (g_, sum)] end
                   | (g_, sum)
                       -> let rec invertMon =
                            function 
                                     | (g_,
                                        (Mon
                                          (n, ((EVar (r, _, _, _), s) :: []))
                                          as mon),
                                        sum) -> begin
                                         if Whnf.isPatSub s then
                                         let ss = Whnf.invert s
                                           in let rhs_ = toFgn sum in begin
                                                if
                                                Unify.invertible
                                                (g_, (rhs_, id), ss, r) then
                                                (Some (mon, ss, sum)) else
                                                None end
                                         else None end
                                     | (g_, mon, sum) -> None
                            in begin
                               match findMon invertMon (g_, sum)
                               with 
                                    | Some
                                        (Mon (n1, ((x1_, s1) :: [])), ss1,
                                         sum1)
                                        -> begin
                                           match findMon invertMon (g_, sum1)
                                           with 
                                                | Some
                                                    (Mon
                                                     (n2, ((x2_, s2) :: [])),
                                                     ss2, sum2)
                                                    -> let s =
                                                         Unify.intersection
                                                         (s1, s2)
                                                         in let ss =
                                                              Whnf.invert s
                                                              in let g'_ =
                                                                   Whnf.strengthen
                                                                   (ss, g_)
                                                                   in 
                                                                   let g =
                                                                    gcd
                                                                    (n1, n2)
                                                                    in 
                                                                    let
                                                                    (x1, x2)
                                                                    =
                                                                    solve_gcd
                                                                    (n1, n2)
                                                                    in 
                                                                    let k_ =
                                                                    newEVar
                                                                    (g'_,
                                                                    number ())
                                                                    in 
                                                                    let z_ =
                                                                    newEVar
                                                                    (g'_,
                                                                    number ())
                                                                    in 
                                                                    ((Assign
                                                                    (g_, x1_,
                                                                    toFgn
                                                                    (plusSum
                                                                    ((Sum
                                                                    (zero,
                                                                    [(Mon
                                                                    (quot
                                                                    (n2, g),
                                                                    [(k_, ss)]))])),
                                                                    timesSum
                                                                    ((Sum
                                                                    (x1, [])),
                                                                    (Sum
                                                                    (zero,
                                                                    [(Mon
                                                                    (one,
                                                                    [(z_, ss)]))]))))),
                                                                    ss1))
                                                                    :: 
                                                                    (Assign
                                                                    (g_, x2_,
                                                                    toFgn
                                                                    (plusSum
                                                                    ((Sum
                                                                    (zero,
                                                                    [(Mon
                                                                    (-
                                                                    (quot
                                                                    (n1, g)),
                                                                    [(k_, ss)]))])),
                                                                    timesSum
                                                                    ((Sum
                                                                    (x2, [])),
                                                                    (Sum
                                                                    (zero,
                                                                    [(Mon
                                                                    (one,
                                                                    [(z_, ss)]))]))))),
                                                                    ss2))
                                                                    :: 
                                                                    solveSum
                                                                    (g_,
                                                                    plusSum
                                                                    ((Sum
                                                                    (zero,
                                                                    [(Mon
                                                                    (g,
                                                                    [(z_, ss)]))])),
                                                                    sum2)))
                                                | None
                                                    -> begin
                                                       match divideSum
                                                             (sum1, n1)
                                                       with 
                                                            | Some sum1'
                                                                -> [(Assign
                                                                    (g_, x1_,
                                                                    toFgn
                                                                    (unaryMinusSum
                                                                    sum1'),
                                                                    ss1))]
                                                            | None
                                                                -> [delaySum
                                                                    (g_, sum)]
                                                       end
                                           end
                                    | None -> [delaySum (g_, sum)]
                               end
        and unifySum (g_, sum1, sum2) =
          let rec invertMon
            (g_, Mon (n, (((EVar (r, _, _, _) as lhs_), s) :: [])), sum) =
            begin
            if Whnf.isPatSub s then
            let ss = Whnf.invert s
              in let rhs_ = toFgn (timesSum ((Sum (- n, [])), sum)) in begin
                   if Unify.invertible (g_, (rhs_, id), ss, r) then
                   (Some (g_, lhs_, rhs_, ss)) else None end
            else None end
            in begin
               match minusSum (sum2, sum1)
               with 
                    | Sum (m, []) -> begin
                        if m = zero then (Succeed []) else Fail end
                    | sum -> begin
                        if solvableSum sum then
                        (Succeed (solveSum (g_, sum))) else Fail end
               end
        and toFgn =
          function 
                   | (Sum (m, []) as sum) -> toExp sum
                   | (Sum (m, monL) as sum)
                       -> (FgnExp (! myID, (MyIntsynRep sum)));;
        let rec toInternal arg__1 arg__2 =
          begin
          match (arg__1, arg__2)
          with 
               | (MyIntsynRep sum, ()) -> toExp (normalizeSum sum)
               | (fe, ()) -> raise ((UnexpectedFgnExp fe))
          end;;
        let rec map arg__3 arg__4 =
          begin
          match (arg__3, arg__4)
          with 
               | (MyIntsynRep sum, f)
                   -> toFgn (normalizeSum (mapSum (f, sum)))
               | (fe, _) -> raise ((UnexpectedFgnExp fe))
          end;;
        let rec app arg__5 arg__6 =
          begin
          match (arg__5, arg__6)
          with 
               | (MyIntsynRep sum, f) -> appSum (f, sum)
               | (fe, _) -> raise ((UnexpectedFgnExp fe))
          end;;
        let rec equalTo arg__7 arg__8 =
          begin
          match (arg__7, arg__8)
          with 
               | (MyIntsynRep sum, u2_)
                   -> begin
                      match minusSum (normalizeSum sum, fromExp (u2_, id))
                      with 
                           | Sum (m, []) -> m = zero
                           | _ -> false
                      end
               | (fe, _) -> raise ((UnexpectedFgnExp fe))
          end;;
        let rec unifyWith arg__9 arg__10 =
          begin
          match (arg__9, arg__10)
          with 
               | (MyIntsynRep sum, (g_, u2_))
                   -> unifySum (g_, normalizeSum sum, fromExp (u2_, id))
               | (fe, _) -> raise ((UnexpectedFgnExp fe))
          end;;
        let rec installFgnExpOps () =
          let csid = ! myID
            in let _ = FgnExpStd.ToInternal.install (csid, toInternal)
                 in let _ = FgnExpStd.Map.install (csid, map)
                      in let _ = FgnExpStd.App.install (csid, App_)
                           in let _ =
                                FgnExpStd.UnifyWith.install (csid, unifyWith)
                                in let _ =
                                     FgnExpStd.EqualTo.install
                                     (csid, equalTo) in ();;
        let rec makeFgn (arity, opExp) s_ =
          let rec makeParams =
            function 
                     | 0 -> Nil
                     | n
                         -> (App
                             ((Root ((BVar n), Nil)),
                              makeParams ((Int.( - ) (n, 1)))))
            in let rec makeLam arg__11 arg__12 =
                 begin
                 match (arg__11, arg__12)
                 with 
                      | (e_, 0) -> e_
                      | (e_, n)
                          -> (Lam
                              ((Dec (None, number ())),
                               makeLam e_ ((Int.( - ) (n, 1)))))
                 end
                 in let rec expand =
                      function 
                               | ((Nil, s), arity)
                                   -> (makeParams arity, arity)
                               | ((App (u_, s_), s), arity)
                                   -> let (s'_, arity') =
                                        expand
                                        ((s_, s), (Int.( - ) (arity, 1)))
                                        in ((App
                                             ((EClo
                                               (u_, comp (s, (Shift arity')))),
                                              s'_)),
                                            arity')
                               | ((SClo (s_, s'), s), arity)
                                   -> expand ((s_, comp (s', s)), arity)
                      in let (s'_, arity') = expand ((s_, id), arity)
                           in makeLam (toFgn (opExp s'_)) arity';;
        let rec makeFgnUnary opSum =
          makeFgn (1, function 
                               | App (u_, Nil) -> opSum (fromExp (u_, id)));;
        let rec makeFgnBinary opSum =
          makeFgn
          (2,
           function 
                    | App (u1_, App (u2_, Nil))
                        -> opSum (fromExp (u1_, id), fromExp (u2_, id)));;
        let rec arrow (u_, v_) = (Pi (((Dec (None, u_)), No), v_));;
        let rec init (cs, installF) =
          begin
            myID := cs;
            begin
              numberID :=
                (installF
                 ((ConDec
                   ("integer", None, 0, (Constraint (! myID, solveNumber)),
                    (Uni Type), Kind)),
                  None, [MS.Mnil]));
              begin
                unaryMinusID :=
                  (installF
                   ((ConDec
                     ("~", None, 0,
                      (Foreign (! myID, makeFgnUnary unaryMinusSum)),
                      (Arrow_ (number (), number ())), Type)),
                    (Some ((FX.Prefix FX.maxPrec))), []));
                begin
                  plusID :=
                    (installF
                     ((ConDec
                       ("+", None, 0,
                        (Foreign (! myID, makeFgnBinary plusSum)),
                        (Arrow_ (number (), (Arrow_ (number (), number ())))),
                        Type)),
                      (Some
                       ((FX.Infix (FX.dec (FX.dec FX.maxPrec), FX.left_)))),
                      []));
                  begin
                    minusID :=
                      (installF
                       ((ConDec
                         ("-", None, 0,
                          (Foreign (! myID, makeFgnBinary minusSum)),
                          (Arrow_
                           (number (), (Arrow_ (number (), number ())))),
                          Type)),
                        (Some
                         ((FX.Infix (FX.dec (FX.dec FX.maxPrec), FX.left_)))),
                        []));
                    begin
                      timesID :=
                        (installF
                         ((ConDec
                           ("*", None, 0,
                            (Foreign (! myID, makeFgnBinary timesSum)),
                            (Arrow_
                             (number (), (Arrow_ (number (), number ())))),
                            Type)),
                          (Some ((FX.Infix (FX.dec FX.maxPrec, FX.left_)))),
                          []));
                      begin
                        installFgnExpOps ();()
                        end
                      
                      end
                    
                    end
                  
                  end
                
                end
              
              end
            
            end;;
        end;;
    (* CSManager.ModeSyn *);;
    (* parseNumber str = SOME(conDec) or NONE

       Invariant:
       If str parses to the number n
       then conDec is the (foreign) constant declaration of n
    *);;
    (* solveNumber k = SOME(U)

       Invariant:
       U is the term obtained applying the foreign constant
       corresponding to the number k to an empty spine
    *);;
    (* findMset eq (x, L) =
         SOME (y, L') if there exists y such that eq (x, y)
                         and L ~ (y :: L') (multiset equality)
         NONE if there is no y in L such that eq (x, y)
    *);;
    (* equalMset eq (L, L') = true iff L ~ L' (multiset equality) *);;
    (* toExp sum = U

       Invariant:
       If sum is normal
       G |- U : V and U is the Twelf syntax conversion of sum
    *);;
    (* toExpMon mon = U

       Invariant:
       If mon is normal
       G |- U : V and U is the Twelf syntax conversion of mon
    *);;
    (* toExpEClo (U,s) = U

       Invariant:
       G |- U : V and U is the Twelf syntax conversion of Us
    *);;
    (* compatibleMon (mon1, mon2) = true only if mon1 = mon2 (as monomials) *);;
    (* sameExpW ((U1,s1), (U2,s2)) = T

       Invariant:
       If   G |- s1 : G1    G1 |- U1 : V1    (U1,s1)  in whnf
       and  G |- s2 : G2    G2 |- U2 : V2    (U2,s2)  in whnf
       then T only if U1[s1] = U2[s2] (as expressions)
    *);;
    (* sameExp ((U1,s1), (U2,s2)) = T

       Invariant:
       If   G |- s1 : G1    G1 |- U1 : V1
       and  G |- s2 : G2    G2 |- U2 : V2
       then T only if U1[s1] = U2[s2] (as expressions)
    *);;
    (* sameSpine (S1, S2) = T

       Invariant:
       If   G |- S1 : V > W
       and  G |- S2 : V > W
       then T only if S1 = S2 (as spines)
    *);;
    (* sameSub (s1, s2) = T

       Invariant:
       If   G |- s1 : G'
       and  G |- s2 : G'
       then T only if s1 = s2 (as substitutions)
    *);;
    (* plusSum (sum1, sum2) = sum3

       Invariant:
       If   sum1 normal
       and  sum2 normal
       then sum3 normal
       and  sum3 = sum1 + sum2
    *);;
    (* plusSumMon (sum1, mon2) = sum3

       Invariant:
       If   sum1 normal
       and  mon2 normal
       then sum3 normal
       and  sum3 = sum1 + mon2
    *);;
    (* timesSum (sum1, sum2) = sum3

       Invariant:
       If   sum1 normal
       and  sum2 normal
       then sum3 normal
       and  sum3 = sum1 * sum2
    *);;
    (* timesSumMon (sum1, mon2) = sum3

       Invariant:
       If   sum1 normal
       and  mon2 normal
       then sum3 normal
       and  sum3 = sum1 * mon2
    *);;
    (* unaryMinusSum sum = sum'

       Invariant:
       If   sum  normal
       then sum' normal
       and  sum' = ~1 * sum
    *);;
    (* minusSum (sum1, sum2) = sum3

       Invariant:
       If   sum1 normal
       and  sum2 normal
       then sum3 normal
       and  sum3 = sum1 - sum2
    *);;
    (* fromExpW (U, s) = sum

       Invariant:
       If   G' |- s : G    G |- U : V    (U,s)  in whnf
       then sum is the internal representation of U[s] as sum of monomials
       and sum is normal
    *);;
    (* fromExp (U, s) = sum

       Invariant:
       If   G' |- s : G    G |- U : V
       then sum is the internal representation of U[s] as sum of monomials
       and sum is normal
    *);;
    (* normalizeSum sum = sum', where sum' normal and sum' = sum *);;
    (* normalizeMon mon = mon', where mon' normal and mon' = mon *);;
    (* mapSum (f, m + M1 + ...) = m + mapMon(f,M1) + ... *);;
    (* mapMon (f, n * (U1,s1) + ...) = n * f(U1,s1) * ... *);;
    (* solvableSum (m + M1 + ....) =
         true iff the generalized gcd of the coefficients of the Mi
                  divides m
    *);;
    (* findMon f (G, sum) =
         SOME(x) if f(M) = SOME(x) for some monomial M in sum
         NONE    if f(M) = NONE for all monomials M in sum
    *);;
    (* divideSum (sum, k) =
         SOME(sum') if sum is divisible by the scalar k, and sum' = sum/k
         NONE       if sum is not divisible by k
    *);;
    (* delaySum (G, sum) = Delay (U, cnstr)
       where U the foreign expression corresponding to sum
       and cnstr is the constraint G |- sum = 0 : integer
    *);;
    (* unifySum (G, sum1, sum2) = result

       Invariant:
       If   G |- sum1 : number     sum1 normal
       and  G |- sum2 : number     sum2 normal
       then result is the outcome (of type FgnUnify) of solving the
       equation sum1 = sum2 by the (generalized) division theorem.
    *);;
    (* unifySum (G, sum1, sum2) = result

       Invariant:
       If   G |- sum1 : number     sum1 normal
       and  G |- sum2 : number     sum2 normal
       then result is the outcome (of type FgnUnify) of solving the
       equation sum1 = sum2 by gaussian elimination.
    *);;
    (* toFgn sum = U

       Invariant:
       If sum normal
       then U is a foreign expression representing sum.
    *);;
    (* toInternal (fe) = U
       Invariant:
       if fe is (MyIntsynRep sum) and sum : normal
       then U is the Twelf syntax conversion of sum
    *);;
    (* map (fe) f = U'

       Invariant:
       if fe is (MyIntsynRep sum)   sum : normal
       and
         f sum = f (m + mon1 + ... + monN) =
               = m + f (m1 * Us1 * ... * UsM) + ...
               = m + (m1 * (f Us1) * ... * f (UsM))
               = sum'           sum' : normal
       then
         U' is a foreign expression representing sum'
    *);;
    (* app (fe) f = ()

       Invariant:
       if fe is (MyIntsynRep sum)     sum : normal
       and
          sum = m + mon1 + ... monN
          where moni = mi * Usi1 * ... UsiMi
       then f is applied to each Usij
         (since sum : normal, each Usij is in whnf)
    *);;
    (* init (cs, installFunction) = ()
       Initialize the constraint solver.
       installFunction is used to add its signature symbols.
    *);;
    let solver =
      {
      name = "equality/integers";
      keywords = "arithmetic,equality";
      needs = ["Unify"];
      fgnConst = (Some { parse = parseNumber} );
      init;
      reset = function 
                       | () -> ();
      mark = function 
                      | () -> ();
      unwind = function 
                        | () -> ()}
      ;;
    let fromExp = fromExp;;
    let toExp = toExp;;
    let normalize = normalizeSum;;
    let compatibleMon = compatibleMon;;
    let number = number;;
    let rec unaryMinus u_ = toFgn (unaryMinusSum (fromExp (u_, id)));;
    let rec plus (u_, v_) =
      toFgn (plusSum (fromExp (u_, id), fromExp (v_, id)));;
    let rec minus (u_, v_) =
      toFgn (minusSum (fromExp (u_, id), fromExp (v_, id)));;
    let rec times (u_, v_) =
      toFgn (timesSum (fromExp (u_, id), fromExp (v_, id)));;
    let Constant_ = numberExp;;
    end;;
(*! sharing Unify.IntSyn = IntSyn !*);;
(*! structure CSManager : CS_MANAGER !*);;
(*! sharing CSManager.IntSyn = IntSyn !*);;
(* functor CSEqIntegers *);;