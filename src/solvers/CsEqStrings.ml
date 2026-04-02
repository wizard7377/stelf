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
    let rec string () = Root (Const !stringID, Nil)
    let concatID = (ref (-1) : IntSyn.cid ref)
    let rec concatExp (u_, v_) = Root (Const !concatID, App (u_, App (v_, Nil)))
    let rec toString s = ("\"" ^ s) ^ "\""

    let rec stringConDec str =
      ConDec (toString str, None, 0, Normal, string (), Type)

    let rec stringExp str = Root (FgnConst (!myID, stringConDec str), Nil)

    let rec fromString string =
      let len = String.size string in
      begin if
        String.sub (string, 0) = '"' && String.sub (string, len - 1) = '"'
      then Some (String.substring (string, 1, len - 2))
      else None
      end

    let rec parseString string =
      begin match fromString string with
      | Some str -> Some (stringConDec str)
      | None -> None
      end

    let rec solveString (g_, s_, k) = Some (stringExp (Int.toString k))

    type concat_ = Concat of atom list
    and atom = String of string | Exp of IntSyn.eclo

    exception MyIntsynRep of concat_

    let rec extractConcat = function
      | MyIntsynRep concat -> concat
      | fe -> raise (UnexpectedFgnExp fe)

    let rec toExp = function
      | Concat [] -> stringExp ""
      | Concat (String str :: []) -> stringExp str
      | Concat (Exp (u_, Shift 0) :: []) -> u_
      | Concat (Exp (u_, s_) :: []) -> EClo (u_, s_)
      | Concat (a_ :: al_) ->
          concatExp (toExp (Concat [ a_ ]), toExp (Concat al_))

    let rec catConcat = function
      | Concat [], concat2 -> concat2
      | concat1, Concat [] -> concat1
      | Concat al1_, Concat al2_ -> begin
          match (List.rev al1_, al2_) with
          | String str1 :: revAL1', String str2 :: al2'_ ->
              Concat (List.rev revAL1' @ (String (str1 ^ str2) :: al2'_))
          | _, _ -> Concat (al1_ @ al2_)
        end

    let rec fromExpW = function
      | (FgnExp (cs, fe), _) as us_ -> begin
          if cs = !myID then normalize (extractConcat fe)
          else Concat [ Exp us_ ]
        end
      | (Root (FgnConst (cs, conDec), _), _) as us_ -> begin
          if cs = !myID then begin
            match fromString (conDecName conDec) with
            | Some str -> begin
                if str = "" then Concat [] else Concat [ String str ]
              end
          end
          else Concat [ Exp us_ ]
        end
      | us_ -> Concat [ Exp us_ ]

    and fromExp us_ = fromExpW (Whnf.whnf us_)

    and normalize = function
      | Concat [] as concat -> concat
      | Concat (String str :: []) as concat -> concat
      | Concat (Exp us_ :: []) -> fromExp us_
      | Concat (a_ :: al_) ->
          catConcat (normalize (Concat [ a_ ]), normalize (Concat al_))

    let rec mapConcat (f, Concat al_) =
      let rec mapConcat' = function
        | [] -> []
        | Exp (u_, s_) :: al_ -> Exp (f (EClo (u_, s_)), id) :: mapConcat' al_
        | String str :: al_ -> String str :: mapConcat' al_
      in
      Concat (mapConcat' al_)

    let rec appConcat (f, Concat al_) =
      let rec appAtom = function
        | Exp (u_, s_) -> f (EClo (u_, s_))
        | String _ -> ()
      in
      List.app appAtom al_

    type split = Split of string * string
    type decomp = Decomp of string * string list

    let rec index (str1, str2) =
      let max = String.size str2 - String.size str1 in
      let rec index' i =
        begin if i <= max then begin
          if String.isPrefix str1 (String.extract (str2, i, None)) then
            i :: index' (i + 1)
          else index' (i + 1)
        end
        else []
        end
      in
      index' 0

    let rec split (str1, str2) =
      let len = String.size str1 in
      let rec split' i =
        Split
          ( String.extract (str2, 0, Some i),
            String.extract (str2, i + len, None) )
      in
      List.map split' (index (str1, str2))

    let rec sameConcat (Concat al1_, Concat al2_) =
      let rec sameConcat' = function
        | [], [] -> true
        | String str1 :: al1_, String str2 :: al2_ ->
            str1 = str2 && sameConcat' (al1_, al2_)
        | Exp us1_ :: al1_, Exp us2_ :: al2_ ->
            sameExp (us1_, us2_) && sameConcat' (al1_, al2_)
        | _ -> false
      in
      sameConcat' (al1_, al2_)

    and sameExpW = function
      | ((Root (h1_, s1_), s1) as us1_), ((Root (h2_, s2_), s2) as us2_) ->
        begin
          match (h1_, h2_) with
          | BVar k1, BVar k2 -> k1 = k2 && sameSpine ((s1_, s1), (s2_, s2))
          | FVar (n1, _, _), FVar (n2, _, _) ->
              n1 = n2 && sameSpine ((s1_, s1), (s2_, s2))
          | _ -> false
        end
      | ( (((EVar (r1, g1_, v1_, cnstrs1) as u1_), s1) as us1_),
          (((EVar (r2, g2_, v2_, cnstrs2) as u2_), s2) as us2_) ) ->
          r1 == r2 && sameSub (s1, s2)
      | _ -> false

    and sameExp (us1_, us2_) = sameExpW (Whnf.whnf us1_, Whnf.whnf us2_)

    and sameSpine = function
      | (Nil, s1), (Nil, s2) -> true
      | (SClo (s1_, s1'), s1), ss2_ -> sameSpine ((s1_, comp (s1', s1)), ss2_)
      | ss1_, (SClo (s2_, s2'), s2) -> sameSpine (ss1_, (s2_, comp (s2', s2)))
      | (App (u1_, s1_), s1), (App (u2_, s2_), s2) ->
          sameExp ((u1_, s1), (u2_, s2)) && sameSpine ((s1_, s1), (s2_, s2))
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

    let rec toFgnUnify = function
      | MultAssign l_ ->
          IntSyn.Succeed
            (List.map
               (function g_, x_, u_, ss_ -> Assign (g_, x_, u_, ss_))
               l_)
      | MultDelay (ul_, cnstr) ->
          IntSyn.Succeed (List.map (function u_ -> Delay (u_, cnstr)) ul_)
      | Failure -> Fail

    and unifyRigid (g_, Concat al1_, Concat al2_) =
      let rec unifyRigid' = function
        | [], [] -> MultAssign []
        | String str1 :: al1_, String str2 :: al2_ -> begin
            if str1 = str2 then unifyRigid' (al1_, al2_) else Failure
          end
        | ( Exp ((EVar (r, _, _, _) as u1_), s) :: al1_,
            Exp ((Root (FVar _, _) as u2_), _) :: al2_ ) ->
            let ss = Whnf.invert s in
            begin if Unify.invertible (g_, (u2_, id), ss, r) then begin
              match unifyRigid' (al1_, al2_) with
              | MultAssign l -> MultAssign ((g_, u1_, u2_, ss) :: l)
              | Failure -> Failure
            end
            else Failure
            end
        | ( Exp ((Root (FVar _, _) as u1_), _) :: al1_,
            Exp ((EVar (r, _, _, _) as u2_), s) :: al2_ ) ->
            let ss = Whnf.invert s in
            begin if Unify.invertible (g_, (u1_, id), ss, r) then begin
              match unifyRigid' (al1_, al2_) with
              | MultAssign l -> MultAssign ((g_, u2_, u1_, ss) :: l)
              | Failure -> Failure
            end
            else Failure
            end
        | ( Exp ((Root (FVar _, _), _) as us1_) :: al1_,
            Exp ((Root (FVar _, _), _) as us2_) :: al2_ ) -> begin
            if sameExpW (us1_, us2_) then unifyRigid' (al1_, al2_) else Failure
          end
        | ( Exp ((EVar (_, _, _, _), _) as us1_) :: al1_,
            Exp ((EVar (_, _, _, _), _) as us2_) :: al2_ ) -> begin
            if sameExpW (us1_, us2_) then unifyRigid' (al1_, al2_) else Failure
          end
        | _ -> Failure
      in
      unifyRigid' (al1_, al2_)

    let rec unifyString = function
      | g_, Concat (String prefix :: al_), str, cnstr -> begin
          if String.isPrefix prefix str then
            let suffix = String.extract (str, String.size prefix, None) in
            unifyString (g_, Concat al_, suffix, cnstr)
          else Failure
        end
      | g_, Concat al_, str, cnstr ->
          let rec unifyString' = function
            | al_, [] -> (Failure, [])
            | [], Decomp (parse, parsedL) :: [] ->
                (MultAssign [], parse :: parsedL)
            | [], candidates -> (MultDelay ([], cnstr), [])
            | Exp (us1_1, us1_2) :: Exp (us2_1, us2_2) :: al_, _ ->
                ( MultDelay ([ EClo (us1_1, us1_2); EClo (us2_1, us2_2) ], cnstr),
                  [] )
            | Exp ((EVar (r, _, _, _) as u_), s) :: al_, candidates -> begin
                if Whnf.isPatSub s then
                  let rec assign arg__1 arg__2 =
                    begin match (arg__1, arg__2) with
                    | r, [] -> None
                    | ( r,
                        ( _,
                          EVar (r', _, _, _),
                          Root (FgnConst (cs, conDec), Nil),
                          _ )
                        :: l_ ) -> begin
                        if r == r' then fromString (conDecName conDec)
                        else assign r l_
                      end
                    | r, _ :: l_ -> assign r l_
                    end
                  in
                  begin match unifyString' (al_, candidates) with
                  | MultAssign l_, parsed :: parsedL -> begin
                      match assign r l_ with
                      | None ->
                          let ss = Whnf.invert s in
                          let w_ = stringExp parsed in
                          (MultAssign ((g_, u_, w_, ss) :: l_), parsedL)
                      | Some parsed' -> begin
                          if parsed = parsed' then (MultAssign l_, parsedL)
                          else (Failure, [])
                        end
                    end
                  | MultDelay (ul_, cnstr), _ ->
                      (MultDelay (EClo (u_, s) :: ul_, cnstr), [])
                  | Failure, _ -> (Failure, [])
                  end
                else (MultDelay ([ EClo (u_, s) ], cnstr), [])
              end
            | Exp (u_, s_) :: al_, _ ->
                (MultDelay ([ EClo (u_, s_) ], cnstr), [])
            | String str :: [], candidates ->
                let rec successors (Decomp (parse, parsedL)) =
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
            | String str :: al_, candidates ->
                let rec successors (Decomp (parse, parsedL)) =
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
                unifyString' (al_, candidates')
          in
          begin match unifyString' (al_, [ Decomp (str, []) ]) with
          | result, [] -> result
          | result, "" :: [] -> result
          | result, parsedL -> Failure
          end

    let rec unifyConcat (g_, (Concat al1_ as concat1), (Concat al2_ as concat2))
        =
      let u1_ = toFgn concat1 in
      let u2_ = toFgn concat2 in
      let cnstr = ref (Eqn (g_, u1_, u2_)) in
      begin match (al1_, al2_) with
      | [], [] -> MultAssign []
      | [], _ -> Failure
      | _, [] -> Failure
      | String str1 :: [], String str2 :: [] -> begin
          if str1 = str2 then MultAssign [] else Failure
        end
      | Exp ((EVar (r, _, _, _) as u_), s) :: [], _ -> begin
          if Whnf.isPatSub s then
            let ss = Whnf.invert s in
            begin if Unify.invertible (g_, (u2_, id), ss, r) then
              MultAssign [ (g_, u_, u2_, ss) ]
            else MultDelay ([ u1_; u2_ ], cnstr)
            end
          else MultDelay ([ u1_; u2_ ], cnstr)
        end
      | _, Exp ((EVar (r, _, _, _) as u_), s) :: [] -> begin
          if Whnf.isPatSub s then
            let ss = Whnf.invert s in
            begin if Unify.invertible (g_, (u1_, id), ss, r) then
              MultAssign [ (g_, u_, u1_, ss) ]
            else MultDelay ([ u1_; u2_ ], cnstr)
            end
          else MultDelay ([ u1_; u2_ ], cnstr)
        end
      | String str :: [], _ -> unifyString (g_, concat2, str, cnstr)
      | _, String str :: [] -> unifyString (g_, concat1, str, cnstr)
      | _ -> begin
          match unifyRigid (g_, concat1, concat2) with
          | MultAssign _ as result -> result
          | Failure -> begin
              if sameConcat (concat1, concat2) then MultAssign []
              else MultDelay ([ u1_; u2_ ], cnstr)
            end
        end
      end

    and toFgn = function
      | Concat (String str :: []) as concat -> stringExp str
      | Concat (Exp (u_, id) :: []) as concat -> u_
      | concat -> FgnExp (!myID, MyIntsynRep concat)

    let rec toInternal arg__3 arg__4 =
      begin match (arg__3, arg__4) with
      | MyIntsynRep concat, () -> toExp (normalize concat)
      | fe, () -> raise (UnexpectedFgnExp fe)
      end

    let rec map arg__5 arg__6 =
      begin match (arg__5, arg__6) with
      | MyIntsynRep concat, f -> toFgn (normalize (mapConcat (f, concat)))
      | fe, _ -> raise (UnexpectedFgnExp fe)
      end

    let rec app arg__7 arg__8 =
      begin match (arg__7, arg__8) with
      | MyIntsynRep concat, f -> appConcat (f, concat)
      | fe, _ -> raise (UnexpectedFgnExp fe)
      end

    let rec equalTo arg__9 arg__10 =
      begin match (arg__9, arg__10) with
      | MyIntsynRep concat, u2_ ->
          sameConcat (normalize concat, fromExp (u2_, id))
      | fe, _ -> raise (UnexpectedFgnExp fe)
      end

    let rec unifyWith arg__11 arg__12 =
      begin match (arg__11, arg__12) with
      | MyIntsynRep concat, (g_, u2_) ->
          toFgnUnify (unifyConcat (g_, normalize concat, fromExp (u2_, id)))
      | fe, _ -> raise (UnexpectedFgnExp fe)
      end

    let rec installFgnExpOps () =
      let csid = !myID in
      let _ = FgnExpStd.ToInternal.install (csid, toInternal) in
      let _ = FgnExpStd.Map.install (csid, map) in
      let _ = FgnExpStd.App.install (csid, app) in
      let _ = FgnExpStd.UnifyWith.install (csid, unifyWith) in
      let _ = FgnExpStd.EqualTo.install (csid, equalTo) in
      ()

    let rec makeFgn (arity, opExp) s_ =
      let rec makeParams = function
        | 0 -> Nil
        | n -> App (Root (BVar n, Nil), makeParams (n - 1))
      in
      let rec makeLam arg__13 arg__14 =
        begin match (arg__13, arg__14) with
        | e_, 0 -> e_
        | e_, n -> Lam (Dec (None, string ()), makeLam e_ (n - 1))
        end
      in
      let rec expand = function
        | (Nil, s), arity -> (makeParams arity, arity)
        | (App (u_, s_), s), arity ->
            let s'_, arity' = expand ((s_, s), arity - 1) in
            (App (EClo (u_, comp (s, Shift arity')), s'_), arity')
        | (SClo (s_, s'), s), arity -> expand ((s_, comp (s, s')), arity)
      in
      let s'_, arity' = expand ((s_, id), arity) in
      makeLam (toFgn (opExp s'_)) arity'

    let rec makeFgnBinary opConcat =
      makeFgn
        ( 2,
          function
          | App (u1_, App (u2_, Nil)) ->
              opConcat (fromExp (u1_, id), fromExp (u2_, id)) )

    let rec arrow (u_, v_) = Pi ((Dec (None, u_), No), v_)

    let rec init (cs, installF) =
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
                      arrow_ (string (), arrow_ (string (), string ())),
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
