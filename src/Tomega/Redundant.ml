open! Intsyn
open! Intsyn.Lambda_

(* # 1 "src/tomega/Redundant.sig.ml" *)
module Tomega = Lambda_.Tomega
include REDUNDANT

(* # 1 "src/tomega/Redundant.fun.ml" *)
open! Basis

(* Redundancy remover (factoring) *)
(* Author: Adam Poswolsky (ABP) *)
exception Error of string

let () =
  Printexc.register_printer (function Error msg -> Some msg | _ -> None)

module Redundant (Redundant__0 : sig
  module Opsem : OPSEM.OPSEM
end) : REDUNDANT = struct
  exception Error = Error

  (*
     convert:  Tomega.Prg -> Tomega.Prg
     Attempts to eliminate *redundant* cases.
     *)
  module T = Tomega
  module I = IntSyn
  module Opsem = Redundant__0.Opsem

  let optionRefEqual (r1, r2, func) =
    begin if r1 == r2 then true
    else
      begin match (r1, r2) with
      | { contents = None }, { contents = None } -> true
      | { contents = Some p1 }, { contents = Some p2 } -> func (p1, p2)
      | _ -> false
      end
    end

  let rec convert = function
    | T.Lam (d, p) -> T.Lam (d, convert p)
    | T.New p -> T.New (convert p)
    | T.Choose p -> T.Choose (convert p)
    | T.PairExp (m, p) -> T.PairExp (m, convert p)
    | T.PairBlock (rho, p) -> T.PairBlock (rho, convert p)
    | T.PairPrg (p1, p2) -> T.PairPrg (convert p1, convert p2)
    | T.Unit -> T.Unit
    | T.Var x -> T.Var x
    | T.Const x -> T.Const x
    | T.Redex (p, s) -> T.Redex (convert p, convertSpine s)
    | T.Rec (d, p) -> T.Rec (d, convert p)
    | T.Case (T.Cases o) -> T.Case (T.Cases (convertCases o))
    | T.Let (d, p1, p2) -> T.Let (d, convert p1, convert p2)

  and convertSpine = function
    | T.Nil -> T.Nil
    | T.AppExp (i, s) -> T.AppExp (i, convertSpine s)
    | T.AppBlock (i, s) -> T.AppBlock (i, convertSpine s)
    | T.AppPrg (p, s) -> T.AppPrg (convert p, convertSpine s)
    | T.SClo (s, t) -> raise (Error "SClo should not exist")

  and expEqual (e1, e2) = Conv.conv (e1, I.id) (e2, I.id)
  and isubEqual (sub1, sub2) = Conv.convSub sub1 sub2

  and blockEqual = function
    | I.Bidx x, I.Bidx x' -> x = x'
    | I.LVar (r, sub1, (cid, sub2)), I.LVar (r', sub1', (cid', sub2')) ->
        optionRefEqual (r, r', blockEqual)
        && isubEqual (sub1, sub1')
        && cid = cid'
        && isubEqual (sub1', sub2')
    | _ -> false (* Should not occur -- ap 2/18/03 *)

  and decEqual = function
    | T.UDec d1, (T.UDec d2, t2) ->
        Conv.convDec d1 I.id (d2, T.coerceSub t2)
    | T.PDec (_, f1, _, _), (T.PDec (_, f2, _, _), t2) ->
        T.convFor f1 T.id (f2, t2)
    | _ -> false

  and caseEqual = function
    | (psi1, t1, p1) :: o1, ((psi2, t2, p2) :: o2, tAfter) ->
        let t2' = T.comp (T.invertSub tAfter) t2 in
        let t = Opsem.createVarSub psi1 psi2 in
        let t' = T.comp t2' t in
        let doMatch =
          try
            begin
              Opsem.matchSub psi1 t1 t';
              true
            end
          with Opsem.NoMatch -> false
        in
        begin if doMatch then
          let newT = T.normalizeSub t in
          let stillMatch = isSubRenamingOnly newT in
          stillMatch && prgEqual (p1, (p2, cleanSub newT))
        else false
        end
        (* Note:  (Psi1 |- t1: Psi0) *)
        (* Psi1 |- t: Psi2 *)
        (* Psi1 |- t' : Psi_0 *)
    | [], ([], t2) -> true
    | _ -> false
  (* Recall that we (Psi2, t2, P2)[tAfter] = (Psi2, (tAfterInv \circ t2), P2) *)

  and spineEqual = function
    | T.Nil, (T.Nil, t2) -> true
    | T.AppExp (e1, s1), (T.AppExp (e2, s2), t2) ->
        Conv.conv (e1, I.id) (e2, T.coerceSub t2)
        && spineEqual (s1, (s2, t2))
    | T.AppBlock (b1, s1), (T.AppBlock (b2, s2), t2) ->
        blockEqual (b1, I.blockSub b2 (T.coerceSub t2))
        && spineEqual (s1, (s2, t2))
    | T.AppPrg (p1, s1), (T.AppPrg (p2, s2), t2) ->
        prgEqual (p1, (p2, t2)) && spineEqual (s1, (s2, t2))
    | T.SClo (s_, t1), (T.SClo (s, t2a), t2) ->
        raise (Error "SClo should not exist!")
    | _ -> false (* there are no SClo created in converter *)

  and prgEqual = function
    | T.Lam (d1, p1), (T.Lam (d2, p2), t2) ->
        decEqual (d1, (d2, t2)) && prgEqual (p1, (p2, T.dot1 t2))
    | T.New p1, (T.New p2, t2) -> prgEqual (p1, (p2, t2))
    | T.Choose p1, (T.Choose p2, t2) -> prgEqual (p1, (p2, t2))
    | T.PairExp (u1, p1), (T.PairExp (u2, p2), t2) ->
        Conv.conv (u1, I.id) (u2, T.coerceSub t2)
        && prgEqual (p1, (p2, t2))
    | T.PairBlock (b1, p1), (T.PairBlock (b2, p2), t2) ->
        blockEqual (b1, I.blockSub b2 (T.coerceSub t2))
        && prgEqual (p1, (p2, t2))
    | T.PairPrg (p1a, p1b), (T.PairPrg (p2a, p2b), t2) ->
        prgEqual (p1a, (p2a, t2)) && prgEqual (p1b, (p2b, t2))
    | T.Unit, (T.Unit, t2) -> true
    | T.Const lemma1, (T.Const lemma2, _) -> lemma1 = lemma2
    | T.Var x1, (T.Var x2, t2) ->
        begin match getFrontIndex (T.varSub x2 t2) with
        | None -> false
        | Some i -> x1 = i
        end
    | T.Redex (p1, s1), (T.Redex (p2, s2), t2) ->
        prgEqual (p1, (p2, t2)) && spineEqual (s1, (s2, t2))
    | T.Rec (d1, p1), (T.Rec (d2, p2), t2) ->
        decEqual (d1, (d2, t2)) && prgEqual (p1, (p2, T.dot1 t2))
    | T.Case (T.Cases o1), (T.Case (T.Cases o2), t2) ->
        caseEqual (o1, (o2, t2))
    | T.Let (d1, p1a, p1b), (T.Let (d2, p2a, p2b), t2) ->
        decEqual (d1, (d2, t2)) && prgEqual (p1a, (p2a, t2))
    | T.PClo (p1, t1), (T.PClo (p2, t2a), t2b) ->
        raise (Error "PClo should not exist!")
    | ( T.EVar (psi1, p1optRef, f1, _, _, _),
        (T.EVar (psi2, p2optref, f2, _, _, _), t2) ) ->
        raise (Error "No EVARs should exist!")
    | _ -> false
  (* there are no PClo created in converter *)
  (*      | prgEqual ((T.Root (H1, S1)), (T.Root (H2, S2), t2)) =
                (case (H1, H2)
                   of (T.Const lemma1, T.Const lemma2) => ((lemma1=lemma2) andalso (spineEqual(S1, (S2,t2))))
                 |  (T.Var x1, T.Var x2) =>
                           (case getFrontIndex(T.varSub(x2,t2)) of
                              NONE => false
                            | SOME i => ((x1 = i) andalso (spineEqual(S1, (S2,t2)))))
                 |  _ => false)
*)

  and convertCases = function
    | a :: c ->
        let (psi, t, p), c' = removeRedundancy (a, c) in
        (psi, t, convert p) :: convertCases c'
    | c -> c

  and removeRedundancy (c, a) = match a with
    | [] -> (c, [])
    | c' :: rest ->
        let (c'' :: cs) = mergeIfNecessary (c, c') in
        let c''', rest' = removeRedundancy (c'', rest) in
        (c''', cs @ rest')

  and getFrontIndex = function
    | T.Idx k -> Some k
    | T.Prg p -> getPrgIndex p
    | T.Exp u -> getExpIndex u
    | T.Block b -> getBlockIndex b
    | T.Undef -> None

  and getPrgIndex = function
    | T.Var k -> Some k
    | T.Redex (p, T.Nil) -> getPrgIndex p
    | T.PClo (p, t) ->
        begin match getPrgIndex p with
        | None -> None
        | Some i -> getFrontIndex (T.varSub i t)
        end
    | _ -> None
  (* it is possible in the matchSub that we will get PClo under a sub (usually id) *)

  and getExpIndex = function
    | I.Root (I.BVar k, I.Nil) -> Some k
    | I.Redex (u, I.Nil) -> getExpIndex u
    | I.EClo (u, t) ->
        begin match getExpIndex u with
        | None -> None
        | Some i -> getFrontIndex (T.revCoerceFront (I.bvarSub i t))
        end
    | I.Lam (I.Dec (_, u1), u2) as u -> (
        try Some (Whnf.etaContract u) with eta -> None | _ -> None)

  and getBlockIndex = function I.Bidx k -> Some k | _ -> None

  and cleanSub = function
    | T.Shift _ as s -> s
    | T.Dot (ft1, s1) ->
        begin match getFrontIndex ft1 with
        | None -> T.Dot (ft1, cleanSub s1)
        | Some index -> T.Dot (T.Idx index, cleanSub s1)
        end

  and isSubRenamingOnly = function
    | T.Shift n -> true
    | T.Dot (ft1, s1) ->
        begin match getFrontIndex ft1 with None -> false | Some _ -> true
        end
        && isSubRenamingOnly s1

  and mergeSpines = function
    | T.Nil, (T.Nil, t2) -> T.Nil
    | T.AppExp (e1, s1), (T.AppExp (e2, s2), t2) ->
        begin if Conv.conv (e1, I.id) (e2, T.coerceSub t2) then
          T.AppExp (e1, mergeSpines (s1, (s2, t2)))
        else raise (Error "Spine not equal (AppExp)")
        end
    | T.AppBlock (b1, s1), (T.AppBlock (b2, s2), t2) ->
        begin if blockEqual (b1, I.blockSub b2 (T.coerceSub t2)) then
          T.AppBlock (b1, mergeSpines (s1, (s2, t2)))
        else raise (Error "Spine not equal (AppBlock)")
        end
    | T.AppPrg (p1, s1), (T.AppPrg (p2, s2), t2) ->
        begin if prgEqual (p1, (p2, t2)) then
          T.AppPrg (p1, mergeSpines (s1, (s2, t2)))
        else raise (Error "Prg (in App) not equal")
        end
    | T.SClo (s_, t1), (T.SClo (s, t2a), t2) ->
        raise (Error "SClo should not exist!")
    | _ -> raise (Error "Spine are not equivalent")
  (* there are no SClo created in converter *)

  and mergePrgs = function
    | T.Lam (d1, p1), (T.Lam (d2, p2), t2) ->
        begin if decEqual (d1, (d2, t2)) && prgEqual (p1, (p2, T.dot1 t2))
        then T.Lam (d1, p1)
        else raise (Error "Lambda don't match")
        end
    | T.New p1, (T.New p2, t2) ->
        begin if prgEqual (p1, (p2, t2)) then T.New p1
        else raise (Error "New don't match")
        end
    | T.Choose p1, (T.Choose p2, t2) ->
        begin if prgEqual (p1, (p2, t2)) then T.Choose p1
        else raise (Error "Choose don't match")
        end
    | T.PairExp (u1, p1), (T.PairExp (u2, p2), t2) ->
        let t2' = T.coerceSub t2 in
        begin if Conv.conv (u1, I.id) (u2, t2') then
          T.PairExp (u1, mergePrgs (p1, (p2, t2)))
        else raise (Error "cannot merge PairExp")
        end
    | T.PairBlock (b1, p1), (T.PairBlock (b2, p2), t2) ->
        let b2' = I.blockSub b2 (T.coerceSub t2) in
        begin if blockEqual (b1, b2') then
          T.PairBlock (b1, mergePrgs (p1, (p2, t2)))
        else raise (Error "cannot merge PairBlock")
        end
    | T.PairPrg (p1a, p1b), (T.PairPrg (p2a, p2b), t2) ->
        begin if prgEqual (p1a, (p2a, t2)) then
          T.PairPrg (p1a, mergePrgs (p1b, (p2b, t2)))
        else raise (Error "cannot merge PairPrg")
        end
    | T.Unit, (T.Unit, t2) -> T.Unit
    | T.Const lemma1, (T.Const lemma2, _) ->
        begin if lemma1 = lemma2 then T.Const lemma1
        else raise (Error "Constants do not Match.")
        end
    | T.Var x1, (T.Var x2, t2) ->
        begin match getFrontIndex (T.varSub x2 t2) with
        | None -> raise (Error "Variables do not Match.")
        | Some i ->
            begin if x1 = i then T.Var x1
            else raise (Error "Variables do not Match.")
            end
        end
    | T.Redex (p1, s1), (T.Redex (p2, s2), t2) ->
        let newS = mergeSpines (s1, (s2, t2)) in
        begin if prgEqual (p1, (p2, t2)) then T.Redex (p1, newS)
        else raise (Error "Redex Prgs don't match")
        end
    | T.Rec (d1, p1), (T.Rec (d2, p2), t2) ->
        begin if decEqual (d1, (d2, t2)) && prgEqual (p1, (p2, T.dot1 t2))
        then T.Rec (d1, p1)
        else raise (Error "Rec's don't match")
        end
    | T.Case (T.Cases o1), (T.Case (T.Cases (c :: [])), t2) ->
        T.Case (T.Cases (mergeCase (o1, (c, t2))))
    | T.Case o1, (T.Case o2, t2) -> raise (Error "Invariant Violated")
    | T.PClo (p1, t1), (T.PClo (p2, t2a), t2b) ->
        raise (Error "PClo should not exist!")
    | T.Let (d1, p1a, p1b), (T.Let (d2, p2a, p2b), t2) ->
        begin if decEqual (d1, (d2, t2)) && prgEqual (p1a, (p2a, t2)) then
          T.Let (d1, p1a, mergePrgs (p1b, (p2b, T.dot1 t2)))
        else raise (Error "Let don't match")
        end
    | ( T.EVar (psi1, p1optRef, f1, _, _, _),
        (T.EVar (psi2, p2optref, f2, _, _, _), t2) ) ->
        raise (Error "No EVARs should exist!")
    | _ ->
        raise (Error "Redundancy in cases could not automatically be removed.")

  (* there are no PClo created in converter *)
  (* By invariant the second case should be a list of one *)
  (* three possible outcomes -
                   (1) We merge the cases together
                   (2) Cases are incompatible (duplicated)
                   (3) Cases are duplicate but all results are the same
                       which means we need to continue merging
                 *)

  (* check the case now *)
  (*      | mergePrgs ((T.Root (H1, S1)), (T.Root (H2, S2), t2)) =
                (case (H1, H2)
                   of (T.Const lemma1, T.Const lemma2) =>
                     if (lemma1=lemma2) then
                        T.Root (H1, mergeSpines((S1),(S2,t2)))
                     else raise Error ""Roots do not match""
                   |  (T.Var x1, T.Var x2) =>
                           (case getFrontIndex(T.varSub(x2,t2)) of
                              NONE => raise Error ""Root does not Match.""
                            | SOME i =>
                                (if (x1 = i) then
                                   T.Root (T.Var x1, mergeSpines((S1),(S2,t2)))
                                 else
                                   raise Error ""Root does not Match.""))
                   |  _ => raise Error ""Root does not Match."")
*)
  and invertSub s =
    let rec lookup (n, a, p) = match a with
      | T.Shift _ -> None
      | T.Dot (T.Undef, s') -> lookup (n + 1, s', p)
      | T.Dot (ft, s') ->
          begin match getFrontIndex ft with
          | None -> lookup (n + 1, s', p)
          | Some k ->
              begin if k = p then Some n else lookup (n + 1, s', p)
              end
          end
    in
    let rec invertSub'' (p, si) = match p with
      | 0 -> si
      | p ->
          begin match lookup (1, s, p) with
          | Some k -> invertSub'' (p - 1, T.Dot (T.Idx k, si))
          | None -> invertSub'' (p - 1, T.Dot (T.Undef, si))
          end
    in
    let rec invertSub' (n, a) = match a with
      | T.Shift p -> invertSub'' (p, T.Shift n)
      | T.Dot (_, s') -> invertSub' (n + 1, s')
    in
    invertSub' (0, s)

  and printSub = function
    | T.Shift k -> print (("Shift " ^ Int.toString k) ^ "\n")
    | T.Dot (T.Idx k, s) -> begin
        print (("Idx " ^ Int.toString k) ^ " (DOT) ");
        printSub s
      end
    | T.Dot (T.Prg (T.EVar _), s) -> begin
        print "PRG_EVAR (DOT) ";
        printSub s
      end
    | T.Dot (T.Exp (I.EVar _), s) -> begin
        print "EXP_EVAR (DOT) ";
        printSub s
      end
    | T.Dot (T.Prg p, s) -> begin
        print "PRG (DOT) ";
        printSub s
      end
    | T.Dot (T.Exp e, s) -> begin
        print "EXP (DOT) ";
        printSub s
      end
    | T.Dot (T.Block b, s) -> begin
        print "BLOCK (DOT) ";
        printSub s
      end
    | T.Dot (T.Undef, s) -> begin
        print "UNDEF. (DOT) ";
        printSub s
      end

  and mergeCase = function
    | [], c -> raise (Error "Case incompatible, cannot merge")
    | ((psi1, t1, p1) :: o as l), (((psi2, t2, p2), tAfter) as c) ->
        let tAfterInv = T.invertSub tAfter in
        let t3 = T.comp tAfterInv t2 in
        let t = Opsem.createVarSub psi1 psi2 in
        let t' = T.comp t3 t in
        let doMatch =
          try
            begin
              Opsem.matchSub psi1 t1 t';
              true
            end
          with Opsem.NoMatch -> false
        in
        begin if doMatch then
          let newT = T.normalizeSub t in
          let stillMatch = isSubRenamingOnly newT in
          begin if stillMatch then
            (psi1, t1, mergePrgs (p1, (p2, cleanSub newT))) :: o
          else
            begin if length o = 0 then (psi2, t3, p2) :: l
            else (psi1, t1, p1) :: mergeCase (o, c)
            end
            (* We tried all the cases, and we can now add it *)
            (* Try other cases *)
          end
        (* Since the case matches, lets continue the merge on P1 and P2
           * Note that removing the redundancy of other case statements
           * is handled recursively ... see convertCases
           *)
        (* Note that tAfter and newT are both renaming substitutions *)
          else
          begin if length o = 0 then (psi2, t3, p2) :: l
          else (psi1, t1, p1) :: mergeCase (o, c)
          end
          (* We tried all the cases, and we can now add it *)
          (* Try other cases *)
        end

  (*
        val _ = printCtx(Psi1)
        val _ = printCtx(Psi2)
          *)
  (* Psi1 |- P1 : F[t1] *)
  (* Psi2 |- P2 : F[t2] *)
  (* Psi1 |- t1 : Psi1' *)
  (* Psi2 |- t2 : Psi2' *)
  (* By invariant,we assume *)
  (* Psi1' |- tAfter: Psi2' *)
  (* Psi2' |- tAfterInv : Psi1' *)
  (* So now we have
         P1 makes sense in Psi1, t1 goes from Psi1' to Psi1.

         Psi1 |- t1 : Psi1'
         Psi2 |- t3 : Psi1'
         *)
  (* Psi1 |- t : Psi2 *)
  (* Psi1 |- t' : Psi1' *)
  (* If we can get this to match, then Psi1 |- P2[t] *)
  and mergeIfNecessary (((psi1, s1, p1) as c), ((psi2, s2, p2) as c')) =
    let t = Opsem.createVarSub psi1 psi2 in
    let t' = T.comp s2 t in
    let doMatch =
      try
        begin
          Opsem.matchSub psi1 s1 t';
          true
        end
      with Opsem.NoMatch -> false
    in
    begin if not doMatch then [ c; c' ]
    else
      let newT = T.normalizeSub t in
      begin if isSubRenamingOnly newT then
        try [ (psi1, s1, mergePrgs (p1, (p2, cleanSub newT))) ]
        with Error s ->
          raise
            (Error
               (("***WARNING*** -- redundant case automatically ANNIHILATED:  "
               ^ s)
               ^ "\n"))
      else [ c; c' ]
      end
    end
  (* Note that s1 is a substitution s.t.  Psi1 |- s1: Psi0
        and s2 is a substitution s.t.         Psi2 |- s2: Psi0

        It is possible that this property is lost when the case is executed
        with a different Psi0 which can happen during recursive calls
        (as the context grows).

        In that case:
          Psi, Psi1 |- X1...Xn, id{Psi} : Psi, Psi2

        Therefore, the X's are not dependent on the extra Psi introduced
        by recursive calls, which is why they are ignored in matchSub as well.

        We will generate a substitution t s.t. Psi1 |- t: Psi2
        Therefore  Psi1 |- (s2 o t) : Psi0

        And we are trying to match it with
                   Psi1 |- s1 : Psi0

      *)
  (* No EVARs will occur
      | convert (T.PClo (P,t)) = raise Error ""No PClo should exist""  T.PClo (convert P, t) 
      | convert (T.EVar (D, P as ref NONE, F)) = T.EVar (D, P, F)
      | convert (T.EVar (D, ref (SOME P), F)) = convert P  some opsem here 
    *)
  (* (T.SClo (convertSpine S, t)) *)
  (* Note that it doesn't handle blocks *)
  (* convertCases is where the real work comes in *)
  (* will attempt to merge cases together and call convert
     * on what happens in each case
     *)
  (* will be T.Cases nil *)
  (* Returns a list with C (merged with redundant cases) as the head followed by the rest *)
  (* returns NONE if not found *)
  (* getPrgIndex returns NONE if it is not an index *)
  (* getExpIndex returns NONE if it is not an index *)
  (* getBlockIndex returns NONE if it is not an index *)
  (* clean up the renaming substitution,
       this is to allow T.invertSub to appropriately
       think it is a pattern substitution
       *)
  (* determine if t is simply a renaming substitution *)
  (* Note that what we are merging it with will need to go under an extra renaming substitution *)
  (*
     For debug purposes 
    and printCtx(Psi) =
      let
        fun printDec ( T.UDec (I.Dec (SOME(s), E)) ) =  (print s ; print "": ""; print (Print.expToString (T.coerceCtx Psi, E)); print ""\n"" )
          | printDec ( T.UDec (I.BDec (SOME(s), (cid, sub)))) = (print s ; print "":\n"")
          | printDec ( T.UDec (I.ADec (SOME(s), i))) = (print s ; print "":(ADec\n"")
          | printDec ( T.UDec (I.NDec) ) = (print ""(NDec)\n"")
          | printDec ( T.PDec (SOME(s), F)) = (print s ; print "":(PDec)\n"")
      in
        case Psi of
          (I.Null) => (print ""I.Null\n"")
          | (I.Decl (G, D)) =>  (printCtx(G) ; printDec(D))
      end
*)
  (* invertSub s = s'

       Invariant:
       If   G |- s : G'    (and s patsub)
       then G' |- s' : G
       s.t. s o s' = id
    *)
  (* debug *)
  (* We need to return it in terms of the context of the first *)
  (* mergeIfNecessary
   * Simply see if C is the same case as C'
   * If so, try to merge them together and return a list of just the case merged together,
   * otherwise, return a list of both elements.
   *)
end
(* # 1 "src/tomega/Redundant.sml.ml" *)
