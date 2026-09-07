open! Table
open! Intsyn.Lambda_
open! Print.Print_
open! Index.Index_
open! Solvers.Solvers_
open! Compile
open! CompSyn
open! Assign
open! Tabling

(* # 1 "src/opsem/TabledMachine.sig.ml" *)

(* Tabled Abstract Machine      *)
(* Author: Brigitte Pientka     *)
include TABLEDMACHINE
(* signature TABLED *)

(* # 1 "src/opsem/TabledMachine.fun.ml" *)
open! Basis
open Tabledsyn
open AbstractTabled
open MemoTable

(* Abstract Machine for tabling*)
(* Author: Brigitte Pientka *)
(* Based on abstract machine in Absmachine.fun *)
exception Error of string

let () =
  Printexc.register_printer (function Error msg -> Some msg | _ -> None)

module Tabled (Tabled__0 : sig
  (*! structure IntSyn' : INTSYN !*)
  (*! structure CompSyn' : COMPSYN !*)
  (*! sharing CompSyn'.IntSyn = IntSyn' !*)
  module Unify : UNIFY

  (*! sharing Unify.IntSyn = IntSyn' !*)
  module TabledSyn : Tabledsyn.TABLEDSYN

  (*!  sharing TabledSyn.IntSyn = IntSyn' !*)
  module Assign : ASSIGN

  (*!  sharing Assign.IntSyn = IntSyn' !*)
  module Index : INDEX

  (*!  sharing Index.IntSyn = IntSyn' !*)
  module Queue : Queue.QUEUE

  (*! structure TableParam : TABLEPARAM !*)
  (*!  sharing TableParam.IntSyn = IntSyn' !*)
  (*!  sharing TableParam.CompSyn = CompSyn' !*)
  module AbstractTabled : ABSTRACTTABLED.ABSTRACTTABLED

  (*!  sharing AbstractTabled.IntSyn = IntSyn' !*)
  (*! sharing AbstractTabled.TableParam = TableParam !*)
  module MemoTable : MEMOTABLE.MEMOTABLE

  (*!  sharing MemoTable.IntSyn = IntSyn' !*)
  (*!  sharing MemoTable.CompSyn = CompSyn'  !*)
  (*! sharing MemoTable.TableParam = TableParam  !*)
  (* CPrint currently unused *)
  module CPrint : Cprint.CPRINT

  (*!  sharing CPrint.IntSyn = IntSyn' !*)
  (*!  sharing CPrint.CompSyn = CompSyn' !*)
  (* CPrint currently unused *)
  module Print : PRINT
end) : TABLED = struct
  open Tabled__0
  open! TableParam

  (*! structure IntSyn = IntSyn' !*)
  (*! structure CompSyn = CompSyn' !*)
  module Unify = Unify
  module TabledSyn = TabledSyn

  (*! structure TableParam = TableParam !*)
  (*  structure Match = Match*)
  open! struct
    module I = IntSyn
    module C = CompSyn
    module A = AbstractTabled
    module T = TableParam
    module MT = MemoTable
  end

  (* ---------------------------------------------------------------------- *)
  (* Suspended goal: SuspType, s, G, sc, ftrail, answerRef, i

       where
       s is a substitution for the existential variables in D such that G |- s : G, D
       sc        : is the success continuation
       ftrail    : is a forward trail
       answerRef : pointer to potential answers in the memo-table
       i         : Number of answer which already have been consumed  by this
                   current program state

    *)
  type suspType =
    | Loop
    | Divergence of (IntSyn.exp * IntSyn.sub) * CompSyn.dProg

  let suspGoals :
      (suspType
      * (IntSyn.dctx * IntSyn.exp * IntSyn.sub)
      * (CompSyn.pskeleton -> unit)
      * Unify.unifTrail
      * ((IntSyn.sub * IntSyn.sub) * T.answer)
      * int ref)
      list
      ref =
    ref []

  exception Error = Error

  (* ---------------------------------------------------------------------- *)
  let cidFromHead = function I.Const a -> a | I.Def a -> a

  let eqHead = function
    | I.Const a, I.Const a' -> a = a'
    | I.Def a, I.Def a' -> a = a'
    | _ -> false

  let rec append (a, g) = match a with
    | I.Null -> g
    | IntSyn.Decl (g', d) -> IntSyn.Decl (append (g', g), d)

  let rec shift (a, s) = match a with
    | I.Null -> s
    | IntSyn.Decl (g, d) -> I.dot1 (shift (g, s))

  let rec raiseType a1 b1 = match a1, b1 with
    | I.Null, v -> v
    | I.Decl (g, d), v -> raiseType g (I.Lam (d, v))

  let rec compose = function
    | I.Null, g -> g
    | IntSyn.Decl (g, d), g' -> IntSyn.Decl (compose (g, g'), d)

  (* ---------------------------------------------------------------------- *)
  (* We write
       G |- M : g
     if M is a canonical proof term for goal g which could be found
     following the operational semantics.  In general, the
     success continuation sc may be applied to such M's in the order
     they are found.  Backtracking is modeled by the return of
     the success continuation.

     Similarly, we write
       G |- S : r
     if S is a canonical proof spine for residual goal r which could
     be found following the operational semantics.  A success continuation
     sc may be applies to such S's in the order they are found and
     return to indicate backtracking.
    *)
  (* ---------------------------------------------------------------------- *)
  (* ctxToEVarSub D = s

     if D is a context for existential variables,
        s.t. u_1:: A_1,.... u_n:: A_n = D
     then . |- s : D where s = X_n....X_1.id

    *)
  let rec ctxToEVarSub (a, s) = match a with
    | I.Null -> s
    | I.Decl (g, I.Dec (_, a)) ->
        let x = I.newEVar I.Null a in
        I.Dot (I.Exp x, ctxToEVarSub (g, s))

  let rec ctxToAVarSub (a, s) = match a with
    | I.Null -> s
    | I.Decl (g, I.Dec (_, a)) ->
        let x = I.newEVar I.Null a in
        I.Dot (I.Exp x, ctxToAVarSub (g, s))
    | I.Decl (g, I.ADec (_, d)) ->
        let x = I.newAVar () in
        I.Dot (I.Exp (I.EClo (x, I.Shift (-d))), ctxToAVarSub (g, s))

  (* ---------------------------------------------------------------------- *)
  (* Solving  variable definitions *)
  (* solveEqn ((VarDef, s), G) = bool

    if G'' |- VarDef and G  . |- s : G''
       G   |- VarDef[s]
    then
       return true, if VarDefs are solvable
              false otherwise
 *)
  let rec solveEqn (a, g) = match a with
    | (trivial, s) -> true
    | (T.Unify (g', e1, n, eqns), s) ->
        let g'' = append (g', g) in
        let s' = shift (g'', s) in
        Assign.unifiable g'' (n, s') (e1, s') && solveEqn ((eqns, s), g)
  (* G, G' |- s' : D, G, G' *)
  (* . |- s : D *)
  (* D, G, G' |- e1 and D, G, G' |- N and D, G |- eqns *)

  let unifySub' (g, s1, s2) =
    try
      begin
        Unify.unifySub g s1 s2;
        true
      end
    with Unify.Unify msg -> false

  let unify g us us' =
    try
      begin
        Unify.unify g us us';
        true
      end
    with Unify.Unify msg -> false

  let rec getHypGoal = function
    | (C.DProg _ as dp), (C.Atom p, s) -> (dp, (p, s))
    | C.DProg (g_, dPool), (C.Impl (r, a, ha, g), s) ->
        let d' = IntSyn.Dec (None, I.EClo (a, s)) in
        begin if !TableParam.strengthen then
          begin match MT.memberCtx g_ (I.EClo (a, s)) g_ with
          | Some _ ->
              let (C.Atom p) = g in
              let x = I.newEVar g_ (I.EClo (a, s)) in
              getHypGoal (C.DProg (g_, dPool), (g, I.Dot (I.Exp x, s)))
              (* is g always atomic? *)
          | None ->
              getHypGoal
                ( C.DProg (I.Decl (g_, d'), I.Decl (dPool, C.Dec (r, s, ha))),
                  (g, I.dot1 s) )
          end
        else
          getHypGoal
            ( C.DProg (I.Decl (g_, d'), I.Decl (dPool, C.Dec (r, s, ha))),
              (g, I.dot1 s) )
        end
    | C.DProg (g_, dPool), (C.All (d, g), s) ->
        let d' = I.decSub d s in
        getHypGoal
          ( C.DProg (I.Decl (g_, d'), I.Decl (dPool, C.Parameter)),
            (g, I.dot1 s) )

  let updateGlobalTable goal flag =
    let (C.DProg (g, dPool) as dProg), (p, s) =
      getHypGoal (C.DProg (I.Null, I.Null), (goal, I.id))
    in
    let g', dAVars, dEVars, u', eqn', s' = A.abstractEVarCtx dProg p s in
    ignore begin if solveEqn ((eqn', s'), g') then ()
      else print "\nresidual equation not solvable!\n"
      end;
    let status =
      begin if flag then TableParam.Complete else TableParam.Incomplete
      end
    in
    begin if TabledSyn.keepTable (IntSyn.targetFam u') then
      begin match MT.callCheck dAVars dEVars g' u' eqn' status with
      | T.RepeatedEntry (_, answRef, _) ->
          TableParam.globalTable :=
            (dAVars, dEVars, g', u', eqn', answRef, status)
            :: !TableParam.globalTable
      | _ -> raise (Error "Top level goal should always in the table\n")
      end
    else ()
    end

  let keepTable c = TabledSyn.keepTable c

  let fillTable () =
    let rec insert = function
      | [] -> ()
      | (dAVars, dEVars, g', u', eqn', answRef, status) :: rest ->
          begin match
            MT.insertIntoTree dAVars dEVars g' u' eqn' answRef status
          with
          | T.NewEntry _ -> insert rest
          | _ -> ()
          end
    in
    insert !TableParam.globalTable

  (*------------------------------------------------------------------------------------------*)
  (* retrieve' ((G, U, s), asub, AnswerList, sc) = ()

     retrieval for subsumption must take into account the asub substitution

     Invariants:
     if
       Goal:                        Answer substitution from index:
       D   |- Pi G. U
       .   |- s : D        and      D' |- s1 : D1
       D   |- asub : D1    and      .  |- s1' : D' (reinstantiate evars)

                                scomp = s1 o s1'
                                  .  |- scomp : D1

       .  |- [esub]asub : D1  where
       .  |- esub : D      and  G |- esub^|G| : D , G
       .  |- s : D         and  G |- s^|G| : D, G
     then
       unify (G, esub^|G|, s^|G|) and unify (G, ([esub]asub)^|G|, scomp^|G|)
       if unification succeeds
         then we continue solving the success continuation.
         otherwise we fail

     Effects: instantiation of EVars in s, s1' and esub
     any effect  sc O1  might have

   *)
  let rec retrieve' (b, c, d, sc) = match b, c, d with
    | (g, u, s), asub, [] -> ()
    | (g, u, s), (esub, asub), ((d', s1), o1) :: a_ ->
        let s1' =
          ctxToEVarSub (d', I.Shift (I.ctxLength d'))
          (* I.id *)
        in
        let scomp = I.comp s1 s1' in
        let ss = shift (g, s) in
        let ss1 = shift (g, scomp) in
        let a = I.comp asub s in
        let ass = shift (g, a) in
        let easub = I.comp asub esub in
        CsManager.trail (function () ->
            begin if
              unifySub' (g, shift (g, esub), ss)
              && unifySub' (g, shift (g, I.comp asub esub), ss1)
            then sc o1
            else ()
            end);
        retrieve' ((g, u, s), (esub, asub), a_, sc)

  (* currently not used -- however, it may be better to not use the same retrieval function for
      subsumption and variant retrieval, and we want to revive this function *)
  (* retrieveV ((G, U, s), answerList, sc)
      if
        . |- [s]Pi G.U
        . |- s : DAVars, DEVars

        ((DEVars_i, s_i), O_i) is an element in answer list
         DEVars_i |- s_i : DAVars, DEVars
         and O_i is a proof skeleton
      then
        sc O_i is evaluated
        Effects: instantiation of EVars in s

   *)
  let rec retrieveV (a, b, sc) = match a, b with
    | (g, u, s), [] -> ()
    | (g, u, s), ((dEVars, s1), o1) :: a ->
        let s1' =
          ctxToEVarSub (dEVars, I.Shift (I.ctxLength dEVars))
          (* I.id *)
        in
        let scomp = I.comp s1 s1' in
        let ss = shift (g, s) in
        let ss1 = shift (g, scomp) in
        CsManager.trail (function () ->
            begin if unifySub' (g, ss, ss1) then sc o1 else ()
            end);
        retrieveV ((g, u, s), a, sc)
  (* for subsumption we must combine it with asumb!!! *)

  let retrieveSW ((g, u, s), asub, answL, sc) =
    retrieve' ((g, u, s), asub, answL, sc)

  (* currently not used -- however, it may be better to  not use the same retrieval function for
      subsumption and variant retrieval, and we want to revive this function *)
  (* fun retrieveSW ((G, U, s), asub, AnswL, sc) =
     case (!TableParam.strategy) of
       TableParam.Variant =>  retrieveV ((G, U, s), AnswL, sc)
     | TableParam.Subsumption => retrieve' ((G, U, s), asub, AnswL, sc) *)
  (* retrieve (k, (G, s), (asub, answRef), sc) = ()
      Invariants:
      If
         G |-   s : G, D   where s contains free existential variables defined in D
         answRef is a pointer to the AnswerList

        G |- asub : D, G  asub is the identity in the variant case
        G |- asub : D, G  asub instantiates existential variables in s.

     then the success continuation sc is triggered.

     Effects: instantiation of EVars in s, and asub
   *)
  let retrieve (k, (g, u, s), (asub, answRef), sc) =
    let lkp = T.lookup answRef in
    let asw' = List.take (rev (T.solutions answRef), T.lookup answRef) in
    let answ' = List.drop (asw', !k) in
    k := lkp;
    retrieveSW ((g, u, s), asub, answ', sc)

  (* ---------------------------------------------------------------------- *)
  (* solve ((g, s), dp, sc) => ()
     Invariants:
     dp = (G, dPool) where  G ~ dPool  (context G matches dPool)
     G |- s : G'
     G' |- g  goal
     if  G |- M : g[s]
       then  sc M  is evaluated
     Effects: instantiation of EVars in g, s, and dp
     any effect  sc M  might have
     *)
  let solve_fn_ref :
      ((CompSyn.goal * IntSyn.sub) * CompSyn.dProg * (CompSyn.pskeleton -> unit) ->
      unit)
      ref =
    ref (fun _ -> failwith "solve_fn not yet initialized")

  let rec solve a1 a2 b2 c2 = match (a1, a2), b2, c2 with
    | (C.Atom p, s), (C.DProg (g, dPool) as dp), sc ->
        begin if TabledSyn.tabledLookup (I.targetFam p) then
          let g', dAVars, dEVars, u', eqn', s' =
            A.abstractEVarCtx dp p s
          in
          ignore begin if solveEqn ((eqn', s'), g') then ()
            else
              print
                "\n\
                 residual equation not solvable! -- This should never happen! \n"
            end;
          begin match
            MT.callCheck dAVars dEVars g' u' eqn' T.Incomplete
          with
          | T.NewEntry answRef ->
              matchAtom
                ( (p, s),
                  dp,
                  function
                  | pskeleton ->
                      begin match MT.answerCheck s' answRef pskeleton with
                      | repeated -> ()
                      | new_ -> sc pskeleton
                      end )
          | T.RepeatedEntry (asub, answRef, Incomplete) ->
              begin if T.noAnswers answRef then begin
                suspGoals :=
                  ( Loop,
                    (g', u', s'),
                    sc,
                    Unify.suspend (),
                    (asub, answRef),
                    ref 0 )
                  :: !suspGoals;
                ()
              end
              else
                let le = T.lookup answRef in
                suspGoals :=
                  ( Loop,
                    (g', u', s'),
                    sc,
                    Unify.suspend (),
                    (asub, answRef),
                    ref le )
                  :: !suspGoals;
                retrieve (ref 0, (g', u', s'), (asub, answRef), sc)
              end
          | T.RepeatedEntry (asub, answRef, Complete) ->
              begin if T.noAnswers answRef then ()
              else retrieve (ref 0, (g', u', s'), (asub, answRef), sc)
              end
          | T.DivergingEntry (asub, answRef) -> begin
              suspGoals :=
                ( Divergence ((p, s), dp),
                  (g', u', s'),
                  sc,
                  Unify.suspend (),
                  ((I.id, asub) (* this is a hack *), answRef),
                  ref 0 )
                :: !suspGoals;
              ()
            end
          end
          (* Side effect: D', G' |- U' added to Table.

              Invariant about abstraction:
              Pi DAVars. Pi DEVars. Pi G'. U'    : abstracted linearized goal
              .  |- s' : DAVars, DEVars             k = |G'|
              G' |- s'^k : DAVars, DEVars, G'
               . |- [s'](Pi G'. U')     and  G |- [s'^k]U' = [s]p *)
        else matchAtom ((p, s), dp, sc)
        end
    | (C.Impl (r, a, ha, g), s), C.DProg (g_, dPool), sc ->
        let d' = I.Dec (None, I.EClo (a, s)) in
        begin if !TableParam.strengthen then
          begin match MT.memberCtx g_ (I.EClo (a, s)) g_ with
          | Some _ ->
              let x = I.newEVar g_ (I.EClo (a, s)) in
              !solve_fn_ref
                ( (g, I.Dot (I.Exp x, s)),
                  C.DProg (g_, dPool),
                  function o -> sc o )
          | None ->
              !solve_fn_ref
                ( (g, I.dot1 s),
                  C.DProg (I.Decl (g_, d'), I.Decl (dPool, C.Dec (r, s, ha))),
                  function o -> sc o )
          end
        else
          !solve_fn_ref
            ( (g, I.dot1 s),
              C.DProg (I.Decl (g_, d'), I.Decl (dPool, C.Dec (r, s, ha))),
              function o -> sc o )
        end
    | (C.All (d, g), s), C.DProg (g_, dPool), sc ->
        let d' = I.decSub d s in
        !solve_fn_ref
          ( (g, I.dot1 s),
            C.DProg (I.Decl (g_, d'), I.Decl (dPool, C.Parameter)),
            function o -> sc o )

  and rSolve (ps', a, b, sc) = match a, b with
    | (C.Eq q, s), C.DProg (g, dPool) ->
        begin if Unify.unifiable g ps' (q, s) then sc [] else ()
        end
    | (C.Assign (q, eqns), s), (C.DProg (g, dPool) as dp) ->
        begin match Assign.assignable g ps' (q, s) with
        | Some cnstr -> aSolve ((eqns, s), dp, cnstr, function s -> sc s)
        | None -> ()
        end
    | (C.And (r, a, g), s), (C.DProg (g_, dPool) as dp) ->
        let x = I.newEVar g_ (I.EClo (a, s)) in
        rSolve
          ( ps',
            (r, I.Dot (I.Exp x, s)),
            dp,
            function
            | s1 -> !solve_fn_ref ((g, s), dp, function s2 -> sc (s1 @ s2))
          )
        (* is this EVar redundant? -fp *)
    | (C.Exists (I.Dec (_, a), r), s), (C.DProg (g, dPool) as dp) ->
        let x = I.newEVar g (I.EClo (a, s)) in
        rSolve (ps', (r, I.Dot (I.Exp x, s)), dp, function s -> sc s)
    | (C.Axists (I.ADec (Some x, d), r), s), (C.DProg (g, dPool) as dp) ->
        let x' = I.newAVar () in
        rSolve (ps', (r, I.Dot (I.Exp (I.EClo (x', I.Shift (-d))), s)), dp, sc)
  (* we don't increase the proof term here! *)
  (* fail *)

  and aSolve (a, b, cnstr, sc) = match a, b with
    | (trivial, s), dp ->
        begin if Assign.solveCnstr cnstr then sc [] else ()
        end
    | (C.UnifyEq (g', e1, n, eqns), s), (C.DProg (g, dPool) as dp)
      ->
        let g'' = append (g', g) in
        let s' = shift (g', s) in
        begin if Assign.unifiable g'' (n, s') (e1, s') then
          aSolve ((eqns, s), dp, cnstr, sc)
        else ()
        end

  and matchAtom (((I.Root (ha, s_), s) as ps'), (C.DProg (g, dPool) as dp), sc)
      =
    let rec matchSig = function
      | [] -> ()
      | (I.Const c as hc) :: sgn' ->
          let (C.SClause r) = C.sProgLookup (cidFromHead hc) in
          CsManager.trail (function () ->
              rSolve (ps', (r, I.id), dp, function s -> sc (C.Pc c :: s)));
          matchSig sgn'
      (* trail to undo EVar instantiations *)
      (* return indicates failure *)
    in
    let rec matchDProg (a, b, k) = match a, b with
      | I.Null, I.Null -> matchSig (Index.lookup (cidFromHead ha))
      | I.Decl (g, _), I.Decl (dPool', C.Dec (r, s, ha')) ->
          begin if eqHead (ha, ha') then begin
            CsManager.trail (function () ->
                rSolve
                  ( ps',
                    (r, I.comp s (I.Shift k)),
                    dp,
                    function s -> sc (C.Dc k :: s) ));
            matchDProg (g, dPool', k + 1)
          end
          else matchDProg (g, dPool', k + 1)
          end
      | I.Decl (g, _), I.Decl (dPool', parameter) ->
          matchDProg (g, dPool', k + 1)
      (* dynamic program exhausted, try signature *)
    in
    let rec matchConstraint (solve_fn, try_) =
      let succeeded =
        CsManager.trail (function () ->
            begin match solve_fn (g, I.SClo (s_, s), try_) with
            | Some u -> begin
                sc [ C.Csolver u ];
                true
              end
            | None -> false
            end)
      in
      begin if succeeded then matchConstraint (solve_fn, try_ + 1) else ()
      end
    in
    begin match I.constStatus (cidFromHead ha) with
    | I.Constraint (cs, solve_fn) -> matchConstraint (solve_fn, 0)
    | _ -> matchDProg (g, dPool, 1)
    end

  (* matchSig [c1,...,cn] = ()
           try each constant ci in turn for solving atomic goal ps', starting
           with c1.
        *)
  (* matchDProg (dPool, k) = ()
           where k is the index of dPool in global dPool from call to matchAtom.
           Try each local assumption for solving atomic goal ps', starting
           with the most recent one.
        *)

  (* rsolve ((p,s'), (r,s), dp, sc) = ()
    Invariants:
    dp = (G, dPool) where G ~ dPool
    G |- s : G'
    G' |- r  resgoal
    G |- s' : G''
    G'' |- p : H @ S' (mod whnf)
    if G |- S : r[s]
       then sc S is evaluated
     Effects: instantiation of EVars in p[s'], r[s], and dp
     any effect  sc S  might have
     *)
  (* aSolve ((ag, s), dp, sc) = res
     Invariants:
       dp = (G, dPool) where G ~ dPool
       G |- s : G'
       if G |- ag[s] auxgoal
       then sc () is evaluated with return value res
       else res = Fail
     Effects: instantiation of EVars in ag[s], dp and sc () *)
  (* matchatom ((p, s), dp, sc) => ()
     Invariants:
       dp = (G, dPool) where G ~ dPool
       G |- s : G'
       G' |- p : type, p = H @ S mod whnf
       if G |- M :: p[s]
       then sc M is evaluated
     Effects: instantiation of EVars in p[s] and dp
              any effect  sc M  might have

     This first tries the local assumptions in dp then
     the static signature.
  *)
  (* retrieval ((p, s), dp, sc, answRef, n) => ()
     Invariants:
     dp = (G, dPool) where  G ~ dPool  (context G matches dPool)
     G |- s : G'
     G' |- p  goal
     answRef : pointer to corresponding answer list
     n       : #number of answers which were already consumed
               by the current goal

     if answers are available
      then retrieve all new answers
     else fail
     *)
  let retrieval (a, b, sc, c, n) = match a, b, c with
    | Loop, (g', u', s'), (asub, answRef) ->
        begin if T.noAnswers answRef then ()
        else retrieve (n, (g', u', s'), (asub, answRef), sc)
        end
    | Divergence ((p, s), dp), (g', u', s'), (asub, answRef) ->
        matchAtom
          ( (p, s),
            dp,
            function
            | pskeleton ->
                begin match MT.answerCheck s' answRef pskeleton with
                | repeated -> ()
                | new_ -> sc pskeleton
                end )

  let tableSize () = MT.tableSize ()
  let suspGoalNo () = List.length !suspGoals

  (*  nextStage () = bool
     Side effect: advances lookup pointers
   *)
  let nextStage () =
    let rec resume = function
      | [] -> ()
      | (susp, s, sc, trail, (asub, answRef), k) :: goals -> begin
          CsManager.trail (function () ->
              begin
                Unify.resume trail;
                retrieval (susp, s, sc, (asub, answRef), k)
              end);
          resume goals
        end
    in
    let sg = rev !suspGoals in
    begin if MT.updateTable () then begin
      TableParam.stageCtr := !TableParam.stageCtr + 1;
      begin
        resume sg;
        true
      end
    end
    else false
    end
  (* table changed during previous stage *)
  (* table did not change during previous stage *)

  let reset () =
    begin
      suspGoals := [];
      begin
        MT.reset ();
        TableParam.stageCtr := 0
      end
    end

  let solveQuery ((g, s), (C.DProg (g_, dPool) as dp), sc) =
    !solve_fn_ref ((g, s), dp, sc)
  (* only works when query is atomic -- if query is not atomic,
      then the subordination relation might be extended and strengthening may not be sound *)

  (* local ... *)
  let () = solve_fn_ref := solveQuery
end
(*!  sharing Print.IntSyn = IntSyn' !*)
(*              structure Names : NAMES *)
(*!  sharing Names.IntSyn = IntSyn' !*)
(*! structure CsManager : CS_MANAGER !*)
(*!  sharing CsManager.IntSyn = IntSyn'!*)
(* functor Tabled *)
(* # 1 "src/opsem/TabledMachine.sml.ml" *)
