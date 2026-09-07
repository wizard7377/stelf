open! Intsyn.Lambda_
open! Modes.Modes_

(* # 1 "src/solvers/CsEqBools.sig.ml" *)

(* # 1 "src/solvers/CsEqBools.fun.ml" *)
open! Basis

module CsEqBools (CSEqBools__0 : sig
  (* Booleans Equation Solver *)
  (* Author: Roberto Virga *)
  (*! structure IntSyn : INTSYN !*)
  module Whnf : WHNF

  (*! sharing Whnf.IntSyn = IntSyn !*)
  module Unify : UNIFY
end) : Cs.CS = struct
  (*! structure CsManager = CsManager !*)
  module Unify = CSEqBools__0.Unify

  (*! structure IntSyn = IntSyn !*)
  type 'a set = 'a list

  (* Set                        *)
  type sum_ = Sum of bool * mon_ set
  and mon_ = Mon of (IntSyn.exp * IntSyn.sub) set

  (* Sum :                      *)
  (* Sum ::= m + M1 + ...       *)
  (* Monomials:                 *)
  (* Mon ::= U1[s1] * ...       *)
  (* A monomial (U1[s1] * U2[s2] * ...) is said to be normal iff
       (a) each (Ui,si) is in whnf and not a foreign term corresponding
           to a sum;
       (b) the terms Ui[si] are pairwise distinct.
     A sum is normal iff all its monomials are normal, and moreover they
     are pairwise distinct.
  *)
  open! struct
    open IntSyn
    module FX = CsManager.Fixity
    module MS = ModeSyn

    exception MyIntsynRep of sum_

    let extractSum = function
      | MyIntsynRep sum -> sum
      | fe -> raise (UnexpectedFgnExp fe)

    let myID = (ref (-1) : csid ref)
    let boolID = (ref (-1) : cid ref)
    let bool () = Root (Const !boolID, Nil)
    let trueID = (ref (-1) : cid ref)
    let falseID = (ref (-1) : cid ref)
    let trueExp () = Root (Const !trueID, Nil)
    let falseExp () = Root (Const !falseID, Nil)

    let solveBool (g, s, k) = match k with
      | 0 -> Some (trueExp ())
      | 1 -> Some (falseExp ())
      | k -> None

    let notID = (ref (-1) : cid ref)
    let xorID = (ref (-1) : cid ref)
    let andID = (ref (-1) : cid ref)
    let orID = (ref (-1) : cid ref)
    let impliesID = (ref (-1) : cid ref)
    let iffID = (ref (-1) : cid ref)
    let notExp u = Root (Const !notID, App (u, Nil))
    let xorExp (u, v) = Root (Const !xorID, App (u, App (v, Nil)))
    let andExp (u, v) = Root (Const !andID, App (u, App (v, Nil)))
    let orExp (u, v) = Root (Const !orID, App (u, App (v, Nil)))
    let impliesExp (u, v) = Root (Const !impliesID, App (u, App (v, Nil)))
    let iffExp (u, v) = Root (Const !iffID, App (u, App (v, Nil)))
    let member eq (x, l) = List.exists (function y -> eq (x, y)) l

    let differenceSet eq (l1, l2) =
      let l1' = List.filter (function x -> not (member eq (x, l2))) l1 in
      let l2' = List.filter (function x -> not (member eq (x, l1))) l2 in
      l1' @ l2'

    let equalSet eq (l1, l2) =
      begin match differenceSet eq (l1, l2) with
      | [] -> true
      | _ :: _ -> false
      end

    let unionSet eq (l1, l2) =
      let l2' = List.filter (function x -> not (member eq (x, l1))) l2 in
      l1 @ l2'

    let rec toExp = function
      | Sum (m, []) ->
          let cid =
            begin if m then !trueID else !falseID
            end
          in
          Root (Const cid, Nil)
      | Sum (m, mon :: []) ->
          begin if m = false then toExpMon mon
          else xorExp (toExp (Sum (m, [])), toExpMon mon)
          end
      | Sum (m, (mon :: monL as monLL)) ->
          xorExp (toExp (Sum (m, monL)), toExpMon mon)

    and toExpMon = function
      | Mon (us :: []) -> toExpEClo us
      | Mon (us :: usL) -> andExp (toExpMon (Mon usL), toExpEClo us)

    and toExpEClo (u, s) = match s with Shift 0 -> u | s -> EClo (u, s)

    let rec compatibleMon (Mon usL1, Mon usL2) =
      equalSet (function us1, us2 -> sameExp (us1, us2)) (usL1, usL2)

    and sameExpW = function
      | ((Root (h1, s1_), s1) as us1), ((Root (h2, s2_), s2) as us2) ->
          begin match (h1, h2) with
          | BVar k1, BVar k2 -> k1 = k2 && sameSpine ((s1_, s1), (s2_, s2))
          | FVar (n1, _, _), FVar (n2, _, _) ->
              n1 = n2 && sameSpine ((s1_, s1), (s2_, s2))
          | _ -> false
          end
      | ( (((EVar (r1, g1, v1, cnstrs1) as u1), s1) as us1),
          (((EVar (r2, g2, v2, cnstrs2) as u2), s2) as us2) ) ->
          r1 == r2 && sameSub (s1, s2)
      | _ -> false

    and sameExp (us1, us2) = sameExpW (Whnf.whnf us1, Whnf.whnf us2)

    and sameSpine = function
      | (Nil, s1), (Nil, s2) -> true
      | (SClo (s1_, s1'), s1), ss2 -> sameSpine ((s1_, comp s1' s1), ss2)
      | ss1, (SClo (s2_, s2'), s2) -> sameSpine (ss1, (s2_, comp s2' s2))
      | (App (u1, s1_), s1), (App (u2, s2_), s2) ->
          sameExp ((u1, s1), (u2, s2)) && sameSpine ((s1_, s1), (s2_, s2))
      | _ -> false

    and sameSub = function
      | Shift _, Shift _ -> true
      | Dot (Idx k1, s1), Dot (Idx k2, s2) -> k1 = k2 && sameSub (s1, s2)
      | (Dot (Idx _, _) as s1), Shift k2 ->
          sameSub (s1, Dot (Idx (k2 + 1), Shift (k2 + 1)))
      | Shift k1, (Dot (Idx _, _) as s2) ->
          sameSub (Dot (Idx (k1 + 1), Shift (k1 + 1)), s2)
      | _ -> false

    let xorSum (Sum (m1, monL1), Sum (m2, monL2)) =
      Sum (not (m1 = m2), differenceSet compatibleMon (monL1, monL2))

    let rec andSum = function
      | (Sum (false, []) as sum1), sum2 -> sum1
      | sum1, (Sum (false, []) as sum2) -> sum2
      | (Sum (true, []) as sum1), sum2 -> sum2
      | sum1, (Sum (true, []) as sum2) -> sum1
      | Sum (m1, mon1 :: monL1), sum2 ->
          xorSum (andSumMon (sum2, mon1), andSum (Sum (m1, monL1), sum2))

    and andSumMon = function
      | Sum (true, []), mon -> Sum (false, [ mon ])
      | (Sum (false, []) as sum1), mon -> sum1
      | Sum (m1, Mon usL1 :: monL1), (Mon usL2 as mon2) ->
          let usL = unionSet sameExp (usL1, usL2) in
          xorSum (Sum (false, [ Mon usL ]), andSumMon (Sum (m1, monL1), mon2))

    let notSum (Sum (m, monL)) = Sum (not m, monL)
    let orSum (sum1, sum2) = xorSum (sum1, xorSum (sum2, andSum (sum1, sum2)))
    let impliesSum (sum1, sum2) = notSum (xorSum (sum1, andSum (sum1, sum2)))
    let iffSum (sum1, sum2) = notSum (xorSum (sum1, sum2))

    let rec fromExpW = function
      | (FgnExp (cs, fe), _) as us ->
          begin if cs = !myID then normalizeSum (extractSum fe)
          else Sum (false, [ Mon [ us ] ])
          end
      | us -> Sum (false, [ Mon [ us ] ])

    and fromExp us = fromExpW (Whnf.whnf us)

    and normalizeSum = function
      | Sum (m, []) as sum -> sum
      | Sum (m, mon :: []) -> xorSum (Sum (m, []), normalizeMon mon)
      | Sum (m, mon :: monL) ->
          xorSum (normalizeMon mon, normalizeSum (Sum (m, monL)))

    and normalizeMon = function
      | Mon (us :: []) -> fromExp us
      | Mon (us :: usL) -> andSum (fromExp us, normalizeMon (Mon usL))

    and mapSum (f, Sum (m, monL)) =
      Sum (m, List.map (function mon -> mapMon (f, mon)) monL)

    and mapMon (f, Mon usL) =
      Mon
        (List.map (function u, s -> Whnf.whnf (f (EClo (u, s)), id)) usL)

    let rec appSum (f, Sum (m, monL)) =
      List.app (function mon -> appMon (f, mon)) monL

    and appMon (f, Mon usL) =
      List.app (function u, s -> f (EClo (u, s))) usL

    let findMon f (g, Sum (m, monL)) =
      let rec findMon' (a, monL2) = match a with
        | [] -> None
        | mon :: monL1 ->
            begin match f (g, mon, Sum (m, monL1 @ monL2)) with
            | Some _ as result -> result
            | None -> findMon' (monL1, mon :: monL2)
            end
      in
      findMon' (monL, [])

    let rec unifySum (g, sum1, sum2) =
      let invertMon = function
        | g, Mon (((EVar (r, _, _, _) as lhs), s) :: []), sum ->
            begin if Whnf.isPatSub s then
              let ss = Whnf.invert s in
              let rhs = toFgn sum in
              begin if Unify.invertible g (rhs, id) ss r then
                Some (g, lhs, rhs, ss)
              else None
              end
            else None
            end
        | _ -> None
      in
      begin match xorSum (sum2, sum1) with
      | Sum (false, []) -> Succeed []
      | Sum (true, []) -> Fail
      | sum ->
          begin match findMon invertMon (g, sum) with
          | Some (g_a, lhs_a, rhs_a, ss_a) ->
              Succeed [ Assign (g_a, lhs_a, rhs_a, ss_a) ]
          | None ->
              let u = toFgn sum in
              let cnstr = ref (Eqn (g, u, falseExp ())) in
              Succeed [ Delay (u, cnstr) ]
          end
      end

    and toFgn = function
      | Sum (m, []) as sum -> toExp sum
      | Sum (m, monL) as sum -> FgnExp (!myID, MyIntsynRep sum)

    let toInternal arg__1 arg__2 =
      begin match (arg__1, arg__2) with
      | MyIntsynRep sum, () -> toExp (normalizeSum sum)
      | fe, () -> raise (UnexpectedFgnExp fe)
      end

    let map arg__3 arg__4 =
      begin match (arg__3, arg__4) with
      | MyIntsynRep sum, f -> toFgn (normalizeSum (mapSum (f, sum)))
      | fe, _ -> raise (UnexpectedFgnExp fe)
      end

    let app arg__5 arg__6 =
      begin match (arg__5, arg__6) with
      | MyIntsynRep sum, f -> appSum (f, sum)
      | fe, _ -> raise (UnexpectedFgnExp fe)
      end

    let equalTo arg__7 arg__8 =
      begin match (arg__7, arg__8) with
      | MyIntsynRep sum, u2 ->
          begin match xorSum (normalizeSum sum, fromExp (u2, id)) with
          | Sum (m, []) -> m = false
          | _ -> false
          end
      | fe, _ -> raise (UnexpectedFgnExp fe)
      end

    let unifyWith arg__9 arg__10 =
      begin match (arg__9, arg__10) with
      | MyIntsynRep sum, (g, u2) ->
          unifySum (g, normalizeSum sum, fromExp (u2, id))
      | fe, _ -> raise (UnexpectedFgnExp fe)
      end

    let installFgnExpOps () =
      let csid = !myID in
      ignore (FgnExpStd.ToInternal.install csid toInternal);
      ignore (FgnExpStd.Map.install csid map);
      ignore (FgnExpStd.App.install csid app);
      ignore (FgnExpStd.UnifyWith.install csid unifyWith);
      ignore (FgnExpStd.EqualTo.install csid equalTo);
      ()

    let makeFgn (arity, opExp) s_ =
      let rec makeParams = function
        | 0 -> Nil
        | n -> App (Root (BVar n, Nil), makeParams (n - 1))
      in
      let rec makeLam arg__11 arg__12 =
        begin match (arg__11, arg__12) with
        | e, 0 -> e
        | e, n -> Lam (Dec (None, bool ()), makeLam e (n - 1))
        end
      in
      let rec expand a1 b1 = match a1, b1 with
        | (Nil, s), arity -> (makeParams arity, arity)
        | (App (u, s_), s), arity ->
            let s', arity' = expand (s_, s) (arity - 1) in
            (App (EClo (u, comp s (Shift arity')), s'), arity')
        | (SClo (s_, s'), s), arity -> expand (s_, comp s' s) arity
      in
      let s', arity' = expand (s_, id) arity in
      makeLam (toFgn (opExp s')) arity'

    let makeFgnUnary opSum =
      makeFgn (1, function App (u, Nil) -> opSum (fromExp (u, id)))

    let makeFgnBinary opSum =
      makeFgn
        ( 2,
          function
          | App (u1, App (u2, Nil)) ->
              opSum (fromExp (u1, id), fromExp (u2, id)) )

    let arrow u v = Pi ((Dec (None, u), No), v)

    let init (cs, installF) =
      begin
        myID := cs;
        begin
          boolID :=
            installF
              ( ConDec
                  ( "bool",
                    None,
                    0,
                    Constraint (!myID, solveBool),
                    Uni Type,
                    Kind ),
                None,
                [ MS.Mnil ] );
          begin
            trueID :=
              installF
                ( ConDec
                    ( "true",
                      None,
                      0,
                      Foreign (!myID, function _ -> toFgn (Sum (true, []))),
                      bool (),
                      Type ),
                  None,
                  [] );
            begin
              falseID :=
                installF
                  ( ConDec
                      ( "false",
                        None,
                        0,
                        Foreign (!myID, function _ -> toFgn (Sum (false, []))),
                        bool (),
                        Type ),
                    None,
                    [] );
              begin
                notID :=
                  installF
                    ( ConDec
                        ( "!",
                          None,
                          0,
                          Foreign (!myID, makeFgnUnary notSum),
                          arrow_ (bool ()) (bool ()),
                          Type ),
                      Some (FX.Prefix FX.maxPrec),
                      [] );
                begin
                  xorID :=
                    installF
                      ( ConDec
                          ( "||",
                            None,
                            0,
                            Foreign (!myID, makeFgnBinary xorSum),
                            arrow_ (bool ()) (arrow_ (bool ()) (bool ())),
                            Type ),
                        Some (FX.Infix (FX.dec FX.maxPrec, FX.Left)),
                        [] );
                  begin
                    andID :=
                      installF
                        ( ConDec
                            ( "&",
                              None,
                              0,
                              Foreign (!myID, makeFgnBinary andSum),
                              arrow_ (bool ()) (arrow_ (bool ()) (bool ())),
                              Type ),
                          Some (FX.Infix (FX.dec FX.maxPrec, FX.Left)),
                          [] );
                    begin
                      orID :=
                        installF
                          ( ConDec
                              ( "|",
                                None,
                                0,
                                Foreign (!myID, makeFgnBinary orSum),
                                arrow_ (bool ()) (arrow_ (bool ()) (bool ())),
                                Type ),
                            Some (FX.Infix (FX.dec FX.maxPrec, FX.Left)),
                            [] );
                      begin
                        impliesID :=
                          installF
                            ( ConDec
                                ( "=>",
                                  None,
                                  0,
                                  Foreign (!myID, makeFgnBinary impliesSum),
                                  arrow_ (bool ()) (arrow_ (bool ()) (bool ())),
                                  Type ),
                              Some
                                (FX.Infix (FX.dec (FX.dec FX.maxPrec), FX.Left)),
                              [] );
                        begin
                          iffID :=
                            installF
                              ( ConDec
                                  ( "<=>",
                                    None,
                                    0,
                                    Foreign (!myID, makeFgnBinary iffSum),
                                    arrow_ (bool ()) (arrow_ (bool ()) (bool ())),
                                    Type ),
                                Some
                                  (FX.Infix (FX.dec (FX.dec FX.maxPrec), FX.Left)),
                                [] );
                          begin
                            installFgnExpOps ();
                            ()
                          end
                        end
                      end
                    end
                  end
                end
              end
            end
          end
        end
      end
  end

  (* CsManager.ModeSyn *)
  (* member eq (x, L) = true iff there there is a y in L s.t. eq(y, x) *)
  (* differenceSet eq L1 L2 = (L1 \ L2) U (L2 \ L1) *)
  (* equalSet eq (L1, L2) = true iff L1 is equal to L2 (both seen as sets) *)
  (* unionSet eq (L1, L2) = L1 U L2 *)
  (* toExp sum = U

       Invariant:
       If sum is normal
       G |- U : V and U is the Stelf syntax conversion of sum
    *)
  (* toExpMon mon = U

       Invariant:
       If mon is normal
       G |- U : V and U is the Stelf syntax conversion of mon
    *)
  (* toExpEClo (U,s) = U

       Invariant:
       G |- U : V and U is the Stelf syntax conversion of Us
    *)
  (* compatibleMon (mon1, mon2) = true only if mon1 = mon2 (as monomials) *)
  (* sameExpW ((U1,s1), (U2,s2)) = T

       Invariant:
       If   G |- s1 : G1    G1 |- U1 : V1    (U1,s1)  in whnf
       and  G |- s2 : G2    G2 |- U2 : V2    (U2,s2)  in whnf
       then T only if U1[s1] = U2[s2] (as expressions)
    *)
  (* sameExp ((U1,s1), (U2,s2)) = T

       Invariant:
       If   G |- s1 : G1    G1 |- U1 : V1
       and  G |- s2 : G2    G2 |- U2 : V2
       then T only if U1[s1] = U2[s2] (as expressions)
    *)
  (* sameSpine (S1, S2) = T

       Invariant:
       If   G |- S1 : V > W
       and  G |- S2 : V > W
       then T only if S1 = S2 (as spines)
    *)
  (* sameSub (s1, s2) = T

       Invariant:
       If   G |- s1 : G'
       and  G |- s2 : G'
       then T only if s1 = s2 (as substitutions)
    *)
  (* xorSum (sum1, sum2) = sum3

       Invariant:
       If   sum1 normal
       and  sum2 normal
       then sum3 normal
       and  sum3 = sum1 xor sum2
    *)
  (* andSum (sum1, sum2) = sum3

       Invariant:
       If   sum1 normal
       and  sum2 normal
       then sum3 normal
       and  sum3 = sum1 and sum2
    *)
  (* andSumMon (sum1, mon2) = sum3

       Invariant:
       If   sum1 normal
       and  mon2 normal
       then sum3 normal
       and  sum3 = sum1 and mon2
    *)
  (* notSum sum = sum'

       Invariant:
       If   sum  normal
       then sum' normal
       and  sum' = not sum
    *)
  (* orSum (sum1, sum2) = sum3

       Invariant:
       If   sum1 normal
       and  sum2 normal
       then sum3 normal
       and  sum3 = sum1 or sum2
    *)
  (* impliesSum (sum1, sum2) = sum3

       Invariant:
       If   sum1 normal
       and  sum2 normal
       then sum3 normal
       and  sum3 = sum1 implies sum2
    *)
  (* iffSum (sum1, sum2) = sum3

       Invariant:
       If   sum1 normal
       and  sum2 normal
       then sum3 normal
       and  sum3 = sum1 iff sum2
    *)
  (* fromExpW (U, s) = sum

       Invariant:
       If   G' |- s : G    G |- U : V    (U,s)  in whnf
       then sum is the internal representation of U[s] as sum of monomials
       and sum is normal
    *)
  (* normalizeSum sum = sum', where sum' normal and sum' = sum *)
  (* normalizeMon mon = mon', where mon' normal and mon' = mon *)
  (* mapSum (f, m + M1 + ...) = m + mapMon(f,M1) + ... *)
  (* mapMon (f, n * (U1,s1) + ...) = n * f(U1,s1) * ... *)
  (* appSum (f, m + M1 + ...) = ()     and appMon (f, Mi) for each i *)
  (* appMon (f, n * (U1, s1) + ... ) = () and f (Ui[si]) for each i *)
  (* findMon f (G, sum) =
         SOME(x) if f(M) = SOME(x) for some monomial M in sum
         NONE    if f(M) = NONE for all monomials M in sum
    *)
  (* unifySum (G, sum1, sum2) = result

       Invariant:
       If   G |- sum1 : number     sum1 normal
       and  G |- sum2 : number     sum2 normal
       then result is the outcome (of type FgnUnify) of solving the
       equation sum1 = sum2 by gaussian elimination.
    *)
  (* toFgn sum = U

       Invariant:
       If sum normal
       then U is a foreign expression representing sum.
    *)
  (* toInternal (fe) = U

       Invariant:
       if fe is (MyIntsynRep sum) and sum : normal
       then U is the Stelf syntax conversion of sum
    *)
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
    *)
  (* app (fe) f = ()

       Invariant:
       if fe is (MyIntsynRep sum)     sum : normal
       and
          sum = m + mon1 + ... monN
          where moni = mi * Usi1 * ... UsiMi
       then f is applied to each Usij
         (since sum : normal, each Usij is in whnf)
    *)
  (* AK: redundant normalizeSum ? *)
  (* init (cs, installFunction) = ()
       Initialize the constraint solver.
       installFunction is used to add its signature symbols.
    *)
  let solver : CsManager.solver =
    {
      name = "equality/booleans";
      keywords = "booleans,equality";
      needs = [ "Unify" ];
      fgnConst = None;
      init;
      reset = (fun () -> ());
      mark = (fun () -> ());
      unwind = (fun () -> ());
    }
end
(*! sharing Unify.IntSyn = IntSyn !*)
(*! structure CsManager : CS_MANAGER !*)
(*! sharing CsManager.IntSyn = IntSyn !*)
(* functor CsEqBools *)

(* # 1 "src/solvers/CsEqBools.sml.ml" *)
