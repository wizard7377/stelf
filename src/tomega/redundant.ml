(* # 1 "src/tomega/redundant.sig.ml" *)
open! Basis
module Tomega = Lambda_.Tomega

module type REDUNDANT = sig
  exception Error of string

  val convert : Tomega.prg -> Tomega.prg
end

(* # 1 "src/tomega/redundant.fun.ml" *)
open! Opsem
open! Basis

(* Redundancy remover (factoring) *)
(* Author: Adam Poswolsky (ABP) *)
module Redundant (Redundant__0 : sig
  module Opsem : OPSEM
end) : REDUNDANT = struct
  exception Error of string

  (*
     convert:  Tomega.Prg -> Tomega.Prg
     Attempts to eliminate *redundant* cases.
     *)
  module T = Tomega
  module I = IntSyn
  module Opsem = Redundant__0.Opsem

  let rec optionRefEqual (r1, r2, func) =
    begin if r1 == r2 then true
    else begin
      match (r1, r2) with
      | { contents = None }, { contents = None } -> true
      | { contents = Some p1_ }, { contents = Some p2_ } -> func (p1_, p2_)
      | _ -> false
    end
    end

  let rec convert = function
    | T.Lam (d_, p_) -> T.Lam (d_, convert p_)
    | T.New p_ -> T.New (convert p_)
    | T.Choose p_ -> T.Choose (convert p_)
    | T.PairExp (m_, p_) -> T.PairExp (m_, convert p_)
    | T.PairBlock (rho, p_) -> T.PairBlock (rho, convert p_)
    | T.PairPrg (p1_, p2_) -> T.PairPrg (convert p1_, convert p2_)
    | T.Unit -> T.Unit
    | T.Var x -> T.Var x
    | T.Const x -> T.Const x
    | T.Redex (p_, s_) -> T.Redex (convert p_, convertSpine s_)
    | T.Rec (d_, p_) -> T.Rec (d_, convert p_)
    | T.Case (T.Cases o_) -> T.Case (T.Cases (convertCases o_))
    | T.Let (d_, p1_, p2_) -> T.Let (d_, convert p1_, convert p2_)

  and convertSpine = function
    | T.Nil -> T.Nil
    | T.AppExp (i_, s_) -> T.AppExp (i_, convertSpine s_)
    | T.AppBlock (i_, s_) -> T.AppBlock (i_, convertSpine s_)
    | T.AppPrg (p_, s_) -> T.AppPrg (convert p_, convertSpine s_)
    | T.SClo (s_, t) -> raise (Error "SClo should not exist")

  and expEqual (e1_, e2_) = Conv.conv ((e1_, I.id), (e2_, I.id))
  and isubEqual (sub1, sub2) = Conv.convSub (sub1, sub2)

  and blockEqual = function
    | I.Bidx x, I.Bidx x' -> x = x'
    | I.LVar (r, sub1, (cid, sub2)), I.LVar (r', sub1', (cid', sub2')) ->
        optionRefEqual (r, r', blockEqual)
        && isubEqual (sub1, sub1')
        && cid = cid'
        && isubEqual (sub1', sub2')
    | _ -> false (* Should not occur -- ap 2/18/03 *)

  and decEqual = function
    | T.UDec d1_, (T.UDec d2_, t2) ->
        Conv.convDec ((d1_, I.id), (d2_, T.coerceSub t2))
    | T.PDec (_, f1_, _, _), (T.PDec (_, f2_, _, _), t2) ->
        T.convFor ((f1_, T.id), (f2_, t2))
    | _ -> false

  and caseEqual = function
    | (psi1_, t1, p1_) :: o1_, ((psi2_, t2, p2_) :: o2_, tAfter) ->
        let t2' = T.comp (T.invertSub tAfter, t2) in
        let t = Opsem.createVarSub (psi1_, psi2_) in
        let t' = T.comp (t2', t) in
        let doMatch =
          try
            begin
              Opsem.matchSub (psi1_, t1, t');
              true
            end
          with NoMatch -> false
        in
        begin if doMatch then
          let newT = T.normalizeSub t in
          let stillMatch = isSubRenamingOnly newT in
          stillMatch && prgEqual (p1_, (p2_, cleanSub newT))
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
    | T.AppExp (e1_, s1_), (T.AppExp (e2_, s2_), t2) ->
        Conv.conv ((e1_, I.id), (e2_, T.coerceSub t2))
        && spineEqual (s1_, (s2_, t2))
    | T.AppBlock (b1_, s1_), (T.AppBlock (b2_, s2_), t2) ->
        blockEqual (b1_, I.blockSub (b2_, T.coerceSub t2))
        && spineEqual (s1_, (s2_, t2))
    | T.AppPrg (p1_, s1_), (T.AppPrg (p2_, s2_), t2) ->
        prgEqual (p1_, (p2_, t2)) && spineEqual (s1_, (s2_, t2))
    | T.SClo (s_, t1), (T.SClo (s, t2a), t2) ->
        raise (Error "SClo should not exist!")
    | _ -> false (* there are no SClo created in converter *)

  and prgEqual = function
    | T.Lam (d1_, p1_), (T.Lam (d2_, p2_), t2) ->
        decEqual (d1_, (d2_, t2)) && prgEqual (p1_, (p2_, T.dot1 t2))
    | T.New p1_, (T.New p2_, t2) -> prgEqual (p1_, (p2_, t2))
    | T.Choose p1_, (T.Choose p2_, t2) -> prgEqual (p1_, (p2_, t2))
    | T.PairExp (u1_, p1_), (T.PairExp (u2_, p2_), t2) ->
        Conv.conv ((u1_, I.id), (u2_, T.coerceSub t2))
        && prgEqual (p1_, (p2_, t2))
    | T.PairBlock (b1_, p1_), (T.PairBlock (b2_, p2_), t2) ->
        blockEqual (b1_, I.blockSub (b2_, T.coerceSub t2))
        && prgEqual (p1_, (p2_, t2))
    | T.PairPrg (p1a_, p1b_), (T.PairPrg (p2a_, p2b_), t2) ->
        prgEqual (p1a_, (p2a_, t2)) && prgEqual (p1b_, (p2b_, t2))
    | T.Unit, (T.Unit, t2) -> true
    | T.Const lemma1, (T.Const lemma2, _) -> lemma1 = lemma2
    | T.Var x1, (T.Var x2, t2) -> begin
        match getFrontIndex (T.varSub (x2, t2)) with
        | None -> false
        | Some i -> x1 = i
      end
    | T.Redex (p1_, s1_), (T.Redex (p2_, s2_), t2) ->
        prgEqual (p1_, (p2_, t2)) && spineEqual (s1_, (s2_, t2))
    | T.Rec (d1_, p1_), (T.Rec (d2_, p2_), t2) ->
        decEqual (d1_, (d2_, t2)) && prgEqual (p1_, (p2_, T.dot1 t2))
    | T.Case (T.Cases o1_), (T.Case (T.Cases o2_), t2) ->
        caseEqual (o1_, (o2_, t2))
    | T.Let (d1_, p1a_, p1b_), (T.Let (d2_, p2a_, p2b_), t2) ->
        decEqual (d1_, (d2_, t2)) && prgEqual (p1a_, (p2a_, t2))
    | T.PClo (p1_, t1), (T.PClo (p2_, t2a), t2b) ->
        raise (Error "PClo should not exist!")
    | ( T.EVar (psi1_, p1optRef_, f1_, _, _, _),
        (T.EVar (psi2_, p2optref_, f2_, _, _, _), t2) ) ->
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
    | a_ :: c_ ->
        let (psi_, t, p_), c'_ = removeRedundancy (a_, c_) in
        (psi_, t, convert p_) :: convertCases c'_
    | c_ -> c_

  and removeRedundancy = function
    | c_, [] -> (c_, [])
    | c_, c'_ :: rest ->
        let (c''_ :: cs_) = mergeIfNecessary (c_, c'_) in
        let c'''_, rest' = removeRedundancy (c''_, rest) in
        (c'''_, cs_ @ rest')

  and getFrontIndex = function
    | T.Idx k -> Some k
    | T.Prg p_ -> getPrgIndex p_
    | T.Exp u_ -> getExpIndex u_
    | T.Block b_ -> getBlockIndex b_
    | T.Undef -> None

  and getPrgIndex = function
    | T.Var k -> Some k
    | T.Redex (p_, T.Nil) -> getPrgIndex p_
    | T.PClo (p_, t) -> begin
        match getPrgIndex p_ with
        | None -> None
        | Some i -> getFrontIndex (T.varSub (i, t))
      end
    | _ -> None
  (* it is possible in the matchSub that we will get PClo under a sub (usually id) *)

  and getExpIndex = function
    | I.Root (I.BVar k, I.Nil) -> Some k
    | I.Redex (u_, I.Nil) -> getExpIndex u_
    | I.EClo (u_, t) -> begin
        match getExpIndex u_ with
        | None -> None
        | Some i -> getFrontIndex (T.revCoerceFront (I.bvarSub (i, t)))
      end
    | I.Lam (I.Dec (_, u1_), u2_) as u_ -> (
        try Some (Whnf.etaContract u_) with eta_ -> None | _ -> None)

  and getBlockIndex = function I.Bidx k -> Some k | _ -> None

  and cleanSub = function
    | T.Shift _ as s_ -> s_
    | T.Dot (ft1_, s1) -> begin
        match getFrontIndex ft1_ with
        | None -> T.Dot (ft1_, cleanSub s1)
        | Some index -> T.Dot (T.Idx index, cleanSub s1)
      end

  and isSubRenamingOnly = function
    | T.Shift n -> true
    | T.Dot (ft1_, s1) ->
        begin match getFrontIndex ft1_ with None -> false | Some _ -> true
        end
        && isSubRenamingOnly s1

  and mergeSpines = function
    | T.Nil, (T.Nil, t2) -> T.Nil
    | T.AppExp (e1_, s1_), (T.AppExp (e2_, s2_), t2) -> begin
        if Conv.conv ((e1_, I.id), (e2_, T.coerceSub t2)) then
          T.AppExp (e1_, mergeSpines (s1_, (s2_, t2)))
        else raise (Error "Spine not equal (AppExp)")
      end
    | T.AppBlock (b1_, s1_), (T.AppBlock (b2_, s2_), t2) -> begin
        if blockEqual (b1_, I.blockSub (b2_, T.coerceSub t2)) then
          T.AppBlock (b1_, mergeSpines (s1_, (s2_, t2)))
        else raise (Error "Spine not equal (AppBlock)")
      end
    | T.AppPrg (p1_, s1_), (T.AppPrg (p2_, s2_), t2) -> begin
        if prgEqual (p1_, (p2_, t2)) then
          T.AppPrg (p1_, mergeSpines (s1_, (s2_, t2)))
        else raise (Error "Prg (in App) not equal")
      end
    | T.SClo (s_, t1), (T.SClo (s, t2a), t2) ->
        raise (Error "SClo should not exist!")
    | _ -> raise (Error "Spine are not equivalent")
  (* there are no SClo created in converter *)

  and mergePrgs = function
    | T.Lam (d1_, p1_), (T.Lam (d2_, p2_), t2) -> begin
        if decEqual (d1_, (d2_, t2)) && prgEqual (p1_, (p2_, T.dot1 t2)) then
          T.Lam (d1_, p1_)
        else raise (Error "Lambda don't match")
      end
    | T.New p1_, (T.New p2_, t2) -> begin
        if prgEqual (p1_, (p2_, t2)) then T.New p1_
        else raise (Error "New don't match")
      end
    | T.Choose p1_, (T.Choose p2_, t2) -> begin
        if prgEqual (p1_, (p2_, t2)) then T.Choose p1_
        else raise (Error "Choose don't match")
      end
    | T.PairExp (u1_, p1_), (T.PairExp (u2_, p2_), t2) ->
        let t2' = T.coerceSub t2 in
        begin if Conv.conv ((u1_, I.id), (u2_, t2')) then
          T.PairExp (u1_, mergePrgs (p1_, (p2_, t2)))
        else raise (Error "cannot merge PairExp")
        end
    | T.PairBlock (b1_, p1_), (T.PairBlock (b2_, p2_), t2) ->
        let b2'_ = I.blockSub (b2_, T.coerceSub t2) in
        begin if blockEqual (b1_, b2'_) then
          T.PairBlock (b1_, mergePrgs (p1_, (p2_, t2)))
        else raise (Error "cannot merge PairBlock")
        end
    | T.PairPrg (p1a_, p1b_), (T.PairPrg (p2a_, p2b_), t2) -> begin
        if prgEqual (p1a_, (p2a_, t2)) then
          T.PairPrg (p1a_, mergePrgs (p1b_, (p2b_, t2)))
        else raise (Error "cannot merge PairPrg")
      end
    | T.Unit, (T.Unit, t2) -> T.Unit
    | T.Const lemma1, (T.Const lemma2, _) -> begin
        if lemma1 = lemma2 then T.Const lemma1
        else raise (Error "Constants do not match.")
      end
    | T.Var x1, (T.Var x2, t2) -> begin
        match getFrontIndex (T.varSub (x2, t2)) with
        | None -> raise (Error "Variables do not match.")
        | Some i -> begin
            if x1 = i then T.Var x1 else raise (Error "Variables do not match.")
          end
      end
    | T.Redex (p1_, s1_), (T.Redex (p2_, s2_), t2) ->
        let newS = mergeSpines (s1_, (s2_, t2)) in
        begin if prgEqual (p1_, (p2_, t2)) then T.Redex (p1_, newS)
        else raise (Error "Redex Prgs don't match")
        end
    | T.Rec (d1_, p1_), (T.Rec (d2_, p2_), t2) -> begin
        if decEqual (d1_, (d2_, t2)) && prgEqual (p1_, (p2_, T.dot1 t2)) then
          T.Rec (d1_, p1_)
        else raise (Error "Rec's don't match")
      end
    | T.Case (T.Cases o1_), (T.Case (T.Cases (c_ :: [])), t2) ->
        T.Case (T.Cases (mergeCase (o1_, (c_, t2))))
    | T.Case o1_, (T.Case o2_, t2) -> raise (Error "Invariant Violated")
    | T.PClo (p1_, t1), (T.PClo (p2_, t2a), t2b) ->
        raise (Error "PClo should not exist!")
    | T.Let (d1_, p1a_, p1b_), (T.Let (d2_, p2a_, p2b_), t2) -> begin
        if decEqual (d1_, (d2_, t2)) && prgEqual (p1a_, (p2a_, t2)) then
          T.Let (d1_, p1a_, mergePrgs (p1b_, (p2b_, T.dot1 t2)))
        else raise (Error "Let don't match")
      end
    | ( T.EVar (psi1_, p1optRef_, f1_, _, _, _),
        (T.EVar (psi2_, p2optref_, f2_, _, _, _), t2) ) ->
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
                              NONE => raise Error ""Root does not match.""
                            | SOME i =>
                                (if (x1 = i) then
                                   T.Root (T.Var x1, mergeSpines((S1),(S2,t2)))
                                 else
                                   raise Error ""Root does not match.""))
                   |  _ => raise Error ""Root does not match."")
*)
  and invertSub s =
    let rec lookup = function
      | n, T.Shift _, p -> None
      | n, T.Dot (T.Undef, s'), p -> lookup (n + 1, s', p)
      | n, T.Dot (ft_, s'), p -> begin
          match getFrontIndex ft_ with
          | None -> lookup (n + 1, s', p)
          | Some k -> begin if k = p then Some n else lookup (n + 1, s', p) end
        end
    in
    let rec invertSub'' = function
      | 0, si -> si
      | p, si -> begin
          match lookup (1, s, p) with
          | Some k -> invertSub'' (p - 1, T.Dot (T.Idx k, si))
          | None -> invertSub'' (p - 1, T.Dot (T.Undef, si))
        end
    in
    let rec invertSub' = function
      | n, T.Shift p -> invertSub'' (p, T.Shift n)
      | n, T.Dot (_, s') -> invertSub' (n + 1, s')
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
    | T.Dot (T.Prg p_, s) -> begin
        print "PRG (DOT) ";
        printSub s
      end
    | T.Dot (T.Exp e_, s) -> begin
        print "EXP (DOT) ";
        printSub s
      end
    | T.Dot (T.Block b_, s) -> begin
        print "BLOCK (DOT) ";
        printSub s
      end
    | T.Dot (T.Undef, s) -> begin
        print "UNDEF. (DOT) ";
        printSub s
      end

  and mergeCase = function
    | [], c_ -> raise (Error "Case incompatible, cannot merge")
    | ((psi1_, t1, p1_) :: o_ as l_), (((psi2_, t2, p2_), tAfter) as c_) ->
        let tAfterInv = T.invertSub tAfter in
        let t3 = T.comp (tAfterInv, t2) in
        let t = Opsem.createVarSub (psi1_, psi2_) in
        let t' = T.comp (t3, t) in
        let doMatch =
          try
            begin
              Opsem.matchSub (psi1_, t1, t');
              true
            end
          with NoMatch -> false
        in
        begin if doMatch then
          let newT = T.normalizeSub t in
          let stillMatch = isSubRenamingOnly newT in
          begin if stillMatch then
            (psi1_, t1, mergePrgs (p1_, (p2_, cleanSub newT))) :: o_
          else begin
            if length o_ = 0 then (psi2_, t3, p2_) :: l_
            else (psi1_, t1, p1_) :: mergeCase (o_, c_)
          end
            (* We tried all the cases, and we can now add it *)
            (* Try other cases *)
          end
        (* Since the case matches, lets continue the merge on P1 and P2
           * Note that removing the redundancy of other case statements
           * is handled recursively ... see convertCases
           *)
        (* Note that tAfter and newT are both renaming substitutions *)
          else begin
          if length o_ = 0 then (psi2_, t3, p2_) :: l_
          else (psi1_, t1, p1_) :: mergeCase (o_, c_)
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
  and mergeIfNecessary (((psi1_, s1, p1_) as c_), ((psi2_, s2, p2_) as c'_)) =
    let t = Opsem.createVarSub (psi1_, psi2_) in
    let t' = T.comp (s2, t) in
    let doMatch =
      try
        begin
          Opsem.matchSub (psi1_, s1, t');
          true
        end
      with NoMatch -> false
    in
    begin if not doMatch then [ c_; c'_ ]
    else
      let newT = T.normalizeSub t in
      begin if isSubRenamingOnly newT then
        try [ (psi1_, s1, mergePrgs (p1_, (p2_, cleanSub newT))) ]
        with Error s ->
          raise
            (Error
               (("***WARNING*** -- redundant case automatically ANNIHILATED:  "
               ^ s)
               ^ "\n"))
      else [ c_; c'_ ]
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
(* # 1 "src/tomega/redundant.sml.ml" *)
