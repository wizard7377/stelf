open! Intsyn.Lambda_
open! Modes.Modes_

(* # 1 "src/solvers/CsEqStrings.sig.ml" *)

(* # 1 "src/solvers/CsEqStrings.fun.ml" *)
open! Basis

module CsEqStrings (CSEqStrings__0 : sig
  (* String Equation Solver *)
  (* Author: Roberto Virga *)
  (*! structure IntSyn : INTSYN !*)
  module Whnf : WHNF

  (*! sharing Whnf.IntSyn = IntSyn !*)
  module Unify : UNIFY
end) : Cs.CS = struct
  (*! structure CsManager = CsManager !*)
  module Unify = CSEqStrings__0.Unify

  open! struct
    open IntSyn
    module FX = CsManager.Fixity
    module MS = ModeSyn

    let myID = (ref (-1) : IntSyn.csid ref)
    let stringID = (ref (-1) : IntSyn.cid ref)
    let string () = Root (Const !stringID, Nil)
    let concatID = (ref (-1) : IntSyn.cid ref)
    let concatExp (u, v) = Root (Const !concatID, App (u, App (v, Nil)))
    let toString s = ("\"" ^ s) ^ "\""

    let stringConDec str =
      ConDec (toString str, None, 0, Normal, string (), Type)

    let stringExp str = Root (FgnConst (!myID, stringConDec str), Nil)

    let fromString string =
      let len = String.size string in
      begin if
        String.sub (string, 0) = '"' && String.sub (string, len - 1) = '"'
      then Some (String.substring (string, 1, len - 2))
      else None
      end

    let parseString string =
      begin match fromString string with
      | Some str -> Some (stringConDec str)
      | None -> None
      end

    let solveString (g, s, k) = Some (stringExp (Int.toString k))

    type concat_ = Concat of atom list
    and atom = String of string | Exp of IntSyn.eclo

    exception MyIntsynRep of concat_

    let extractConcat = function
      | MyIntsynRep concat -> concat
      | fe -> raise (UnexpectedFgnExp fe)

    let rec toExp = function
      | Concat [] -> stringExp ""
      | Concat (String str :: []) -> stringExp str
      | Concat (Exp (u, Shift 0) :: []) -> u
      | Concat (Exp (u, s) :: []) -> EClo (u, s)
      | Concat (a :: al) -> concatExp (toExp (Concat [ a ]), toExp (Concat al))

    let catConcat = function
      | Concat [], concat2 -> concat2
      | concat1, Concat [] -> concat1
      | Concat al1, Concat al2 ->
          begin match (List.rev al1, al2) with
          | String str1 :: revAL1', String str2 :: al2' ->
              Concat (List.rev revAL1' @ (String (str1 ^ str2) :: al2'))
          | _, _ -> Concat (al1 @ al2)
          end

    let rec fromExpW = function
      | (FgnExp (cs, fe), _) as us ->
          begin if cs = !myID then normalize (extractConcat fe)
          else Concat [ Exp us ]
          end
      | (Root (FgnConst (cs, conDec), _), _) as us ->
          begin if cs = !myID then
            begin match fromString (conDecName conDec) with
            | Some str ->
                begin if str = "" then Concat [] else Concat [ String str ]
                end
            end
          else Concat [ Exp us ]
          end
      | us -> Concat [ Exp us ]

    and fromExp us = fromExpW (Whnf.whnf us)

    and normalize = function
      | Concat [] as concat -> concat
      | Concat (String str :: []) as concat -> concat
      | Concat (Exp us :: []) -> fromExp us
      | Concat (a :: al) ->
          catConcat (normalize (Concat [ a ]), normalize (Concat al))

    let mapConcat (f, Concat al) =
      let rec mapConcat' = function
        | [] -> []
        | Exp (u, s) :: al -> Exp (f (EClo (u, s)), id) :: mapConcat' al
        | String str :: al -> String str :: mapConcat' al
      in
      Concat (mapConcat' al)

    let appConcat (f, Concat al) =
      let appAtom = function
        | Exp (u, s) -> f (EClo (u, s))
        | String _ -> ()
      in
      List.app appAtom al

    type split = Split of string * string
    type decomp = Decomp of string * string list

    let index (str1, str2) =
      let max = String.size str2 - String.size str1 in
      let rec index' i =
        begin if i <= max then
          begin if String.isPrefix str1 (String.extract (str2, i, None)) then
            i :: index' (i + 1)
          else index' (i + 1)
          end
        else []
        end
      in
      index' 0

    let split (str1, str2) =
      let len = String.size str1 in
      let split' i =
        Split
          ( String.extract (str2, 0, Some i),
            String.extract (str2, i + len, None) )
      in
      List.map split' (index (str1, str2))

    let rec sameConcat (Concat al1, Concat al2) =
      let rec sameConcat' = function
        | [], [] -> true
        | String str1 :: al1, String str2 :: al2 ->
            str1 = str2 && sameConcat' (al1, al2)
        | Exp us1 :: al1, Exp us2 :: al2 ->
            sameExp (us1, us2) && sameConcat' (al1, al2)
        | _ -> false
      in
      sameConcat' (al1, al2)

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

    type stringUnify =
      | MultAssign of (dec ctx * exp * exp * sub) list
      | MultDelay of exp list * cnstr_ ref
      | Failure

    let toFgnUnify = function
      | MultAssign l ->
          IntSyn.Succeed
            (List.map
               (function g, x, u, ss -> Assign (g, x, u, ss))
               l)
      | MultDelay (ul, cnstr) ->
          IntSyn.Succeed (List.map (function u -> Delay (u, cnstr)) ul)
      | Failure -> Fail

    and unifyRigid (g, Concat al1, Concat al2) =
      let rec unifyRigid' = function
        | [], [] -> MultAssign []
        | String str1 :: al1, String str2 :: al2 ->
            begin if str1 = str2 then unifyRigid' (al1, al2) else Failure
            end
        | ( Exp ((EVar (r, _, _, _) as u1), s) :: al1,
            Exp ((Root (FVar _, _) as u2), _) :: al2 ) ->
            let ss = Whnf.invert s in
            begin if Unify.invertible g (u2, id) ss r then
              begin match unifyRigid' (al1, al2) with
              | MultAssign l -> MultAssign ((g, u1, u2, ss) :: l)
              | Failure -> Failure
              end
            else Failure
            end
        | ( Exp ((Root (FVar _, _) as u1), _) :: al1,
            Exp ((EVar (r, _, _, _) as u2), s) :: al2 ) ->
            let ss = Whnf.invert s in
            begin if Unify.invertible g (u1, id) ss r then
              begin match unifyRigid' (al1, al2) with
              | MultAssign l -> MultAssign ((g, u2, u1, ss) :: l)
              | Failure -> Failure
              end
            else Failure
            end
        | ( Exp ((Root (FVar _, _), _) as us1) :: al1,
            Exp ((Root (FVar _, _), _) as us2) :: al2 ) ->
            begin if sameExpW (us1, us2) then unifyRigid' (al1, al2)
            else Failure
            end
        | ( Exp ((EVar (_, _, _, _), _) as us1) :: al1,
            Exp ((EVar (_, _, _, _), _) as us2) :: al2 ) ->
            begin if sameExpW (us1, us2) then unifyRigid' (al1, al2)
            else Failure
            end
        | _ -> Failure
      in
      unifyRigid' (al1, al2)

    let rec unifyString (g, a, str, cnstr) = match a with
      | Concat (String prefix :: al) ->
          begin if String.isPrefix prefix str then
            let suffix = String.extract (str, String.size prefix, None) in
            unifyString (g, Concat al, suffix, cnstr)
          else Failure
          end
      | Concat al ->
          let rec unifyString' = function
            | al, [] -> (Failure, [])
            | [], Decomp (parse, parsedL) :: [] ->
                (MultAssign [], parse :: parsedL)
            | [], candidates -> (MultDelay ([], cnstr), [])
            | Exp (us1_1, us1_2) :: Exp (us2_1, us2_2) :: al, _ ->
                ( MultDelay ([ EClo (us1_1, us1_2); EClo (us2_1, us2_2) ], cnstr),
                  [] )
            | Exp ((EVar (r, _, _, _) as u), s) :: al, candidates ->
                begin if Whnf.isPatSub s then
                  let rec assign arg__1 arg__2 =
                    begin match (arg__1, arg__2) with
                    | r, [] -> None
                    | ( r,
                        ( _,
                          EVar (r', _, _, _),
                          Root (FgnConst (cs, conDec), Nil),
                          _ )
                        :: l ) ->
                        begin if r == r' then fromString (conDecName conDec)
                        else assign r l
                        end
                    | r, _ :: l -> assign r l
                    end
                  in
                  begin match unifyString' (al, candidates) with
                  | MultAssign l, parsed :: parsedL ->
                      begin match assign r l with
                      | None ->
                          let ss = Whnf.invert s in
                          let w = stringExp parsed in
                          (MultAssign ((g, u, w, ss) :: l), parsedL)
                      | Some parsed' ->
                          begin if parsed = parsed' then (MultAssign l, parsedL)
                          else (Failure, [])
                          end
                      end
                  | MultDelay (ul, cnstr), _ ->
                      (MultDelay (EClo (u, s) :: ul, cnstr), [])
                  | Failure, _ -> (Failure, [])
                  end
                else (MultDelay ([ EClo (u, s) ], cnstr), [])
                end
            | Exp (u, s) :: al, _ -> (MultDelay ([ EClo (u, s) ], cnstr), [])
            | String str :: [], candidates ->
                let successors (Decomp (parse, parsedL)) =
                  List.mapPartial
                    (function
                      | Split (prefix, "") -> Some (Decomp (prefix, parsedL))
                      | Split (prefix, suffix) -> None)
                    (split (str, parse))
                in
                let candidates' =
                  List.foldr
                    (fun (x__op, y__op) -> x__op @ y__op)
                    []
                    (List.map successors candidates)
                in
                unifyString' ([], candidates')
            | String str :: al, candidates ->
                let successors (Decomp (parse, parsedL)) =
                  List.map
                    (function
                      | Split (prefix, suffix) ->
                          Decomp (suffix, prefix :: parsedL))
                    (split (str, parse))
                in
                let candidates' =
                  List.foldr
                    (fun (x__op, y__op) -> x__op @ y__op)
                    []
                    (List.map successors candidates)
                in
                unifyString' (al, candidates')
          in
          begin match unifyString' (al, [ Decomp (str, []) ]) with
          | result, [] -> result
          | result, "" :: [] -> result
          | result, parsedL -> Failure
          end

    let rec unifyConcat (g, (Concat al1 as concat1), (Concat al2 as concat2)) =
      let u1 = toFgn concat1 in
      let u2 = toFgn concat2 in
      let cnstr = ref (Eqn (g, u1, u2)) in
      begin match (al1, al2) with
      | [], [] -> MultAssign []
      | [], _ -> Failure
      | _, [] -> Failure
      | String str1 :: [], String str2 :: [] ->
          begin if str1 = str2 then MultAssign [] else Failure
          end
      | Exp ((EVar (r, _, _, _) as u), s) :: [], _ ->
          begin if Whnf.isPatSub s then
            let ss = Whnf.invert s in
            begin if Unify.invertible g (u2, id) ss r then
              MultAssign [ (g, u, u2, ss) ]
            else MultDelay ([ u1; u2 ], cnstr)
            end
          else MultDelay ([ u1; u2 ], cnstr)
          end
      | _, Exp ((EVar (r, _, _, _) as u), s) :: [] ->
          begin if Whnf.isPatSub s then
            let ss = Whnf.invert s in
            begin if Unify.invertible g (u1, id) ss r then
              MultAssign [ (g, u, u1, ss) ]
            else MultDelay ([ u1; u2 ], cnstr)
            end
          else MultDelay ([ u1; u2 ], cnstr)
          end
      | String str :: [], _ -> unifyString (g, concat2, str, cnstr)
      | _, String str :: [] -> unifyString (g, concat1, str, cnstr)
      | _ ->
          begin match unifyRigid (g, concat1, concat2) with
          | MultAssign _ as result -> result
          | Failure ->
              begin if sameConcat (concat1, concat2) then MultAssign []
              else MultDelay ([ u1; u2 ], cnstr)
              end
          end
      end

    and toFgn = function
      | Concat (String str :: []) as concat -> stringExp str
      | Concat (Exp (u, id) :: []) as concat -> u
      | concat -> FgnExp (!myID, MyIntsynRep concat)

    let toInternal arg__3 arg__4 =
      begin match (arg__3, arg__4) with
      | MyIntsynRep concat, () -> toExp (normalize concat)
      | fe, () -> raise (UnexpectedFgnExp fe)
      end

    let map arg__5 arg__6 =
      begin match (arg__5, arg__6) with
      | MyIntsynRep concat, f -> toFgn (normalize (mapConcat (f, concat)))
      | fe, _ -> raise (UnexpectedFgnExp fe)
      end

    let app arg__7 arg__8 =
      begin match (arg__7, arg__8) with
      | MyIntsynRep concat, f -> appConcat (f, concat)
      | fe, _ -> raise (UnexpectedFgnExp fe)
      end

    let equalTo arg__9 arg__10 =
      begin match (arg__9, arg__10) with
      | MyIntsynRep concat, u2 ->
          sameConcat (normalize concat, fromExp (u2, id))
      | fe, _ -> raise (UnexpectedFgnExp fe)
      end

    let unifyWith arg__11 arg__12 =
      begin match (arg__11, arg__12) with
      | MyIntsynRep concat, (g, u2) ->
          toFgnUnify (unifyConcat (g, normalize concat, fromExp (u2, id)))
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
      let rec makeLam arg__13 arg__14 =
        begin match (arg__13, arg__14) with
        | e, 0 -> e
        | e, n -> Lam (Dec (None, string ()), makeLam e (n - 1))
        end
      in
      let rec expand a1 b1 = match a1, b1 with
        | (Nil, s), arity -> (makeParams arity, arity)
        | (App (u, s_), s), arity ->
            let s', arity' = expand (s_, s) (arity - 1) in
            (App (EClo (u, comp s (Shift arity')), s'), arity')
        | (SClo (s_, s'), s), arity -> expand (s_, comp s s') arity
      in
      let s', arity' = expand (s_, id) arity in
      makeLam (toFgn (opExp s')) arity'

    let makeFgnBinary opConcat =
      makeFgn
        ( 2,
          function
          | App (u1, App (u2, Nil)) ->
              opConcat (fromExp (u1, id), fromExp (u2, id)) )

    let arrow u v = Pi ((Dec (None, u), No), v)

    let init (cs, installF) =
      begin
        myID := cs;
        begin
          stringID :=
            installF
              ( ConDec
                  ( "string",
                    None,
                    0,
                    Constraint (!myID, solveString),
                    Uni Type,
                    Kind ),
                None,
                [ MS.Mnil ] );
          begin
            concatID :=
              installF
                ( ConDec
                    ( "++",
                      None,
                      0,
                      Foreign (!myID, makeFgnBinary catConcat),
                      arrow_ (string ()) (arrow_ (string ()) (string ())),
                      Type ),
                  Some (FX.Infix (FX.maxPrec, FX.Right)),
                  [] );
            begin
              installFgnExpOps ();
              ()
            end
          end
        end
      end
  end

  (* CsManager.ModeSyn *)
  (* fromString string =
         SOME(str)  if string parses to the string str
         NONE       otherwise
    *)
  (* parseString string = SOME(conDec) or NONE

       Invariant:
       If str parses to the string str
       then conDec is the (foreign) constant declaration of str
    *)
  (* solveString str = SOME(U)

       Invariant:
       U is the term obtained applying the foreign constant
       corresponding to the string str to an empty spine
    *)
  (* Concatenation:             *)
  (* Concat::= A1 ++ A2 ++ ...  *)
  (* Atoms:                     *)
  (* Atom ::= ""str""             *)
  (*        | (U,s)             *)
  (* Internal syntax representation of this module *)
  (* A concatenation is said to be normal if
         (a) it does not contain empty string atoms
         (b) it does not contain two consecutive string atoms
    *)
  (* ... and Exp atoms are in whnf?  - ak *)
  (* toExp concat = U

       Invariant:
       If concat is normal
       G |- U : V and U is the Stelf syntax conversion of concat
    *)
  (* catConcat (concat1, concat2) = concat3

       Invariant:
       If   concat1 normal
       and  concat2 normal
       then concat3 normal
       and  concat3 = concat1 ++ concat2
    *)
  (* fromExpW (U, s) = concat

       Invariant:
       If   G' |- s : G    G |- U : V    (U,s)  in whnf
       then concat is the representation of U[s] as concatenation of atoms
       and  concat is normal
    *)
  (* fromExp (U, s) = concat

       Invariant:
       If   G' |- s : G    G |- U : V
       then concat is the representation of U[s] as concatenation of atoms
       and  concat is normal
    *)
  (* normalize concat = concat', where concat' normal and concat' = concat *)
  (* mapSum (f, A1 + ...) = f(A1) ++ ... *)
  (* appConcat (f, A1 + ... ) = ()  and f(Ui) for Ai = Exp Ui *)
  (* Split:                                         *)
  (* Split ::= str1 ++ str2                         *)
  (* Decomposition:                                 *)
  (* Decomp ::= toParse | [parsed1, ..., parsedn]   *)
  (* index (str1, str2) = [idx1, ..., idxn]
       where the idxk are all the positions in str2 where str1 appear.
    *)
  (* split (str1, str2) = [Split(l1,r1), ..., Split(ln,rn)]
       where, for each k, str2 = lk ++ str1 ++ rk.
    *)
  (* sameConcat (concat1, concat2) =
         true only if concat1 = concat2 (as concatenations)
    *)
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
  (* Unification Result:
       StringUnify ::= {G1 |- X1 := U1[s1], ..., Gn |- Xn := Un[sn]}
                     | {delay U1 on cnstr1, ..., delay Un on cnstrn}
                     | Failure
    *)
  (* toFgnUnify stringUnify = result
       where result is obtained translating stringUnify.
    *)
  (* unifyRigid (G, concat1, concat2) = stringUnify

       Invariant:
       If   G |- concat1 : string    concat1 normal
       and  G |- concat2 : string    concat2 normal
       then if there is an instantiation I :
               s.t. G |- concat1 <I> == concat2 <I>
            then stringUnify = MultAssign I
            else stringUnify = Failure
    *)
  (* FIX: the next two cases are wrong -kw *)
  (* unifyString (G, concat, str, cnstr) = stringUnify

       Invariant:
       If   G |- concat : string    concat1 normal
       then if there is an instantiation I :
               s.t. G |- concat <I> == str
            then stringUnify = MultAssign I
            else if there cannot be any possible such instantiation
            then stringUnify = Failure
            else stringUnify = MultDelay [U1, ..., Un] cnstr
                   where U1, ..., Un are expression to be delayed on cnstr
    *)
  (* unifyConcat (G, concat1, concat2) = stringUnify

       Invariant:
       If   G |- concat1 : string    concat1 normal
       and  G |- concat2 : string    concat2 normal
       then if there is an instantiation I :
               s.t. G |- concat1 <I> == concat2 <I>
            then stringUnify = MultAssign I
            else if there cannot be any possible such instantiation
            then stringUnify = Failure
            else stringUnify = MultDelay [U1, ..., Un] cnstr
                   where U1, ..., Un are expression to be delayed on cnstr
    *)
  (* FIX: the next two cases are wrong -kw *)
  (* toFgn sum = U

       Invariant:
       If sum normal
       then U is a foreign expression representing sum.
    *)
  (* toInternal (fe) = U

       Invariant:
       if fe is (MyIntsynRep concat) and concat : normal
       then U is the Stelf syntax conversion of concat
    *)
  (* map (fe) f = U'

       Invariant:
       if fe is (MyIntsynRep concat)   concat : normal
       and
         f concat = f (A1 ++ ... ++ AN )
                  = f (A1) ++ ... ++ f (AN)
                  = concat'           concat' : normal
       then
         U' is a foreign expression representing concat'
    *)
  (* app (fe) f = ()

       Invariant:
       if fe is (MyIntsynRep concat)     concat : normal
       and
          concat = A1 ++ ... ++ AN
          where some Ai are (Exp Usi)
       then f is applied to each Usi
       (since concat : normal, each Usij is in whnf)
    *)
  (* init (cs, installFunction) = ()
       Initialize the constraint solver.
       installFunction is used to add its signature symbols.
    *)
  let solver : CsManager.solver =
    {
      name = "equality/strings";
      keywords = "strings,equality";
      needs = [ "Unify" ];
      fgnConst = Some { parse = parseString };
      init;
      reset = (fun () -> ());
      mark = (fun () -> ());
      unwind = (fun () -> ());
    }
end
(*! sharing Unify.IntSyn = IntSyn !*)
(*! structure CsManager : CS_MANAGER !*)
(*! sharing CsManager.IntSyn = IntSyn !*)
(* functor CsEqStrings *)

(* # 1 "src/solvers/CsEqStrings.sml.ml" *)
