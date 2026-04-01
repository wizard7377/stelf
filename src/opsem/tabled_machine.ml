(* # 1 "src/opsem/tabled_machine.sig.ml" *)
open! Basis

(* Tabled Abstract Machine      *)
(* Author: Brigitte Pientka     *)
include Tabled_machine_intf
(* signature TABLED *)

(* # 1 "src/opsem/tabled_machine.fun.ml" *)
open! Index
open! Basis
open Tabledsyn
open Abstract_tabled
open Memo_table

(* Abstract Machine for tabling*)
(* Author: Brigitte Pientka *)
(* Based on abstract machine in absmachine.fun *)
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
  module AbstractTabled : Abstract_tabled.ABSTRACTTABLED

  (*!  sharing AbstractTabled.IntSyn = IntSyn' !*)
  (*! sharing AbstractTabled.TableParam = TableParam !*)
  module MemoTable : Memo_table.MEMOTABLE

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
  open! Table_param

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

  let suspGoals_ :
      (suspType
      * (IntSyn.dctx * IntSyn.exp * IntSyn.sub)
      * (CompSyn.pskeleton -> unit)
      * Unify.unifTrail
      * ((IntSyn.sub * IntSyn.sub) * T.answer)
      * int ref)
      list
      ref =
    ref []

  exception Error of string

  (* ---------------------------------------------------------------------- *)
  let rec cidFromHead = function I.Const a -> a | I.Def a -> a

  let rec eqHead = function
    | I.Const a, I.Const a' -> a = a'
    | I.Def a, I.Def a' -> a = a'
    | _ -> false

  let rec append = function
    | I.Null, g_ -> g_
    | IntSyn.Decl (g'_, d_), g_ -> IntSyn.Decl (append (g'_, g_), d_)

  let rec shift = function
    | I.Null, s -> s
    | IntSyn.Decl (g_, d_), s -> I.dot1 (shift (g_, s))

  let rec raiseType = function
    | I.Null, v_ -> v_
    | I.Decl (g_, d_), v_ -> raiseType (g_, I.Lam (d_, v_))

  let rec compose = function
    | I.Null, g_ -> g_
    | IntSyn.Decl (g_, d_), g'_ -> IntSyn.Decl (compose (g_, g'_), d_)

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
  let rec ctxToEVarSub = function
    | I.Null, s -> s
    | I.Decl (g_, I.Dec (_, a_)), s ->
        let x_ = I.newEVar (I.Null, a_) in
        I.Dot (I.Exp x_, ctxToEVarSub (g_, s))

  let rec ctxToAVarSub = function
    | I.Null, s -> s
    | I.Decl (g_, I.Dec (_, a_)), s ->
        let x_ = I.newEVar (I.Null, a_) in
        I.Dot (I.Exp x_, ctxToAVarSub (g_, s))
    | I.Decl (g_, I.ADec (_, d)), s ->
        let x_ = I.newAVar () in
        I.Dot (I.Exp (I.EClo (x_, I.Shift (-d))), ctxToAVarSub (g_, s))

  (* ---------------------------------------------------------------------- *)
  (* Solving  variable definitions *)
  (* solveEqn ((VarDef, s), G) = bool

    if G'' |- VarDef and G  . |- s : G''
       G   |- VarDef[s]
    then
       return true, if VarDefs are solvable
              false otherwise
 *)
  let rec solveEqn = function
    | (trivial_, s), g_ -> true
    | (T.Unify (g'_, e1, n_, eqns), s), g_ ->
        let g''_ = append (g'_, g_) in
        let s' = shift (g''_, s) in
        Assign.unifiable (g''_, (n_, s'), (e1, s')) && solveEqn ((eqns, s), g_)
  (* G, G' |- s' : D, G, G' *)
  (* . |- s : D *)
  (* D, G, G' |- e1 and D, G, G' |- N and D, G |- eqns *)

  let rec unifySub' (g_, s1, s2) =
    try
      begin
        Unify.unifySub (g_, s1, s2);
        true
      end
    with Unify.Unify msg -> false

  let rec unify (g_, us_, us'_) =
    try
      begin
        Unify.unify (g_, us_, us'_);
        true
      end
    with Unify.Unify msg -> false

  let rec getHypGoal = function
    | (C.DProg _ as dp), (C.Atom p, s) -> (dp, (p, s))
    | C.DProg (g_, dPool), (C.Impl (r, a_, ha_, g), s) ->
        let d'_ = IntSyn.Dec (None, I.EClo (a_, s)) in
        begin if !TableParam.strengthen then begin
          match MT.memberCtx ((g_, I.EClo (a_, s)), g_) with
          | Some _ ->
              let (C.Atom p) = g in
              let x_ = I.newEVar (g_, I.EClo (a_, s)) in
              getHypGoal (C.DProg (g_, dPool), (g, I.Dot (I.Exp x_, s)))
              (* is g always atomic? *)
          | None ->
              getHypGoal
                ( C.DProg (I.Decl (g_, d'_), I.Decl (dPool, C.Dec (r, s, ha_))),
                  (g, I.dot1 s) )
        end
        else
          getHypGoal
            ( C.DProg (I.Decl (g_, d'_), I.Decl (dPool, C.Dec (r, s, ha_))),
              (g, I.dot1 s) )
        end
    | C.DProg (g_, dPool), (C.All (d_, g), s) ->
        let d'_ = I.decSub (d_, s) in
        getHypGoal
          ( C.DProg (I.Decl (g_, d'_), I.Decl (dPool, C.Parameter)),
            (g, I.dot1 s) )

  let rec updateGlobalTable (goal, flag) =
    let (C.DProg (g_, dPool) as dProg), (p, s) =
      getHypGoal (C.DProg (I.Null, I.Null), (goal, I.id))
    in
    let g'_, dAVars_, dEVars_, u'_, eqn', s' =
      A.abstractEVarCtx (dProg, p, s)
    in
    let _ =
      begin if solveEqn ((eqn', s'), g'_) then ()
      else print "\nresidual equation not solvable!\n"
      end
    in
    let status =
      begin if flag then TableParam.Complete else TableParam.Incomplete
      end
    in
    begin if TabledSyn.keepTable (IntSyn.targetFam u'_) then begin
      match MT.callCheck (dAVars_, dEVars_, g'_, u'_, eqn', status) with
      | T.RepeatedEntry (_, answRef, _) ->
          TableParam.globalTable :=
            (dAVars_, dEVars_, g'_, u'_, eqn', answRef, status)
            :: !TableParam.globalTable
      | _ -> raise (Error "Top level goal should always in the table\n")
    end
    else ()
    end

  let rec keepTable c = TabledSyn.keepTable c

  let rec fillTable () =
    let rec insert = function
      | [] -> ()
      | (dAVars_, dEVars_, g'_, u'_, eqn', answRef, status) :: rest -> begin
          match
            MT.insertIntoTree (dAVars_, dEVars_, g'_, u'_, eqn', answRef, status)
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
  let rec retrieve' = function
    | (g_, u_, s), asub, [], sc -> ()
    | (g_, u_, s), (esub, asub), ((d'_, s1), o1_) :: a_, sc ->
        let s1' =
          ctxToEVarSub (d'_, I.Shift (I.ctxLength d'_))
          (* I.id *)
        in
        let scomp = I.comp (s1, s1') in
        let ss = shift (g_, s) in
        let ss1 = shift (g_, scomp) in
        let a = I.comp (asub, s) in
        let ass = shift (g_, a) in
        let easub = I.comp (asub, esub) in
        begin
          Cs_manager.trail (function () ->
              begin if
                unifySub' (g_, shift (g_, esub), ss)
                && unifySub' (g_, shift (g_, I.comp (asub, esub)), ss1)
              then sc o1_
              else ()
              end);
          retrieve' ((g_, u_, s), (esub, asub), a_, sc)
        end

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
  let rec retrieveV = function
    | (g_, u_, s), [], sc -> ()
    | (g_, u_, s), ((dEVars_, s1), o1_) :: a_, sc ->
        let s1' =
          ctxToEVarSub (dEVars_, I.Shift (I.ctxLength dEVars_))
          (* I.id *)
        in
        let scomp = I.comp (s1, s1') in
        let ss = shift (g_, s) in
        let ss1 = shift (g_, scomp) in
        begin
          Cs_manager.trail (function () ->
              begin if unifySub' (g_, ss, ss1) then sc o1_ else ()
              end);
          retrieveV ((g_, u_, s), a_, sc)
        end
  (* for subsumption we must combine it with asumb!!! *)

  let rec retrieveSW ((g_, u_, s), asub, answL_, sc) =
    retrieve' ((g_, u_, s), asub, answL_, sc)

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
  let rec retrieve (k, (g_, u_, s), (asub, answRef), sc) =
    let lkp = T.lookup answRef in
    let asw' = List.take (rev (T.solutions answRef), T.lookup answRef) in
    let answ' = List.drop (asw', !k) in
    begin
      k := lkp;
      retrieveSW ((g_, u_, s), asub, answ', sc)
    end

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

  let rec solve = function
    | (C.Atom p, s), (C.DProg (g_, dPool) as dp), sc -> begin
        if TabledSyn.tabledLookup (I.targetFam p) then
          let g'_, dAVars_, dEVars_, u'_, eqn', s' =
            A.abstractEVarCtx (dp, p, s)
          in
          let _ =
            begin if solveEqn ((eqn', s'), g'_) then ()
            else
              print
                "\n\
                 residual equation not solvable! -- This should never happen! \n"
            end
          in
          begin match
            MT.callCheck (dAVars_, dEVars_, g'_, u'_, eqn', T.Incomplete)
          with
          | T.NewEntry answRef ->
              matchAtom
                ( (p, s),
                  dp,
                  function
                  | pskeleton -> begin
                      match MT.answerCheck (s', answRef, pskeleton) with
                      | repeated -> ()
                      | new_ -> sc pskeleton
                    end )
          | T.RepeatedEntry (asub, answRef, Incomplete) -> begin
              if T.noAnswers answRef then begin
                suspGoals_ :=
                  ( Loop,
                    (g'_, u'_, s'),
                    sc,
                    Unify.suspend (),
                    (asub, answRef),
                    ref 0 )
                  :: !suspGoals_;
                ()
              end
              else
                let le = T.lookup answRef in
                begin
                  suspGoals_ :=
                    ( Loop,
                      (g'_, u'_, s'),
                      sc,
                      Unify.suspend (),
                      (asub, answRef),
                      ref le )
                    :: !suspGoals_;
                  retrieve (ref 0, (g'_, u'_, s'), (asub, answRef), sc)
                end
            end
          | T.RepeatedEntry (asub, answRef, Complete) -> begin
              if T.noAnswers answRef then ()
              else retrieve (ref 0, (g'_, u'_, s'), (asub, answRef), sc)
            end
          | T.DivergingEntry (asub, answRef) -> begin
              suspGoals_ :=
                ( Divergence ((p, s), dp),
                  (g'_, u'_, s'),
                  sc,
                  Unify.suspend (),
                  ((I.id, asub) (* this is a hack *), answRef),
                  ref 0 )
                :: !suspGoals_;
              ()
            end
          end
          (* Side effect: D', G' |- U' added to table.

              Invariant about abstraction:
              Pi DAVars. Pi DEVars. Pi G'. U'    : abstracted linearized goal
              .  |- s' : DAVars, DEVars             k = |G'|
              G' |- s'^k : DAVars, DEVars, G'
               . |- [s'](Pi G'. U')     and  G |- [s'^k]U' = [s]p *)
        else matchAtom ((p, s), dp, sc)
      end
    | (C.Impl (r, a_, ha_, g), s), C.DProg (g_, dPool), sc ->
        let d'_ = I.Dec (None, I.EClo (a_, s)) in
        begin if !TableParam.strengthen then begin
          match MT.memberCtx ((g_, I.EClo (a_, s)), g_) with
          | Some _ ->
              let x_ = I.newEVar (g_, I.EClo (a_, s)) in
              !solve_fn_ref
                ( (g, I.Dot (I.Exp x_, s)),
                  C.DProg (g_, dPool),
                  function o_ -> sc o_ )
          | None ->
              !solve_fn_ref
                ( (g, I.dot1 s),
                  C.DProg (I.Decl (g_, d'_), I.Decl (dPool, C.Dec (r, s, ha_))),
                  function o_ -> sc o_ )
        end
        else
          !solve_fn_ref
            ( (g, I.dot1 s),
              C.DProg (I.Decl (g_, d'_), I.Decl (dPool, C.Dec (r, s, ha_))),
              function o_ -> sc o_ )
        end
    | (C.All (d_, g), s), C.DProg (g_, dPool), sc ->
        let d'_ = I.decSub (d_, s) in
        !solve_fn_ref
          ( (g, I.dot1 s),
            C.DProg (I.Decl (g_, d'_), I.Decl (dPool, C.Parameter)),
            function o_ -> sc o_ )

  and rSolve = function
    | ps', (C.Eq q_, s), C.DProg (g_, dPool), sc -> begin
        if Unify.unifiable (g_, ps', (q_, s)) then sc [] else ()
      end
    | ps', (C.Assign (q_, eqns), s), (C.DProg (g_, dPool) as dp), sc -> begin
        match Assign.assignable (g_, ps', (q_, s)) with
        | Some cnstr -> aSolve ((eqns, s), dp, cnstr, function s_ -> sc s_)
        | None -> ()
      end
    | ps', (C.And (r, a_, g), s), (C.DProg (g_, dPool) as dp), sc ->
        let x_ = I.newEVar (g_, I.EClo (a_, s)) in
        rSolve
          ( ps',
            (r, I.Dot (I.Exp x_, s)),
            dp,
            function
            | s1_ -> !solve_fn_ref ((g, s), dp, function s2_ -> sc (s1_ @ s2_))
          )
        (* is this EVar redundant? -fp *)
    | ps', (C.Exists (I.Dec (_, a_), r), s), (C.DProg (g_, dPool) as dp), sc ->
        let x_ = I.newEVar (g_, I.EClo (a_, s)) in
        rSolve (ps', (r, I.Dot (I.Exp x_, s)), dp, function s_ -> sc s_)
    | ( ps',
        (C.Axists (I.ADec (Some x_, d), r), s),
        (C.DProg (g_, dPool) as dp),
        sc ) ->
        let x'_ = I.newAVar () in
        rSolve (ps', (r, I.Dot (I.Exp (I.EClo (x'_, I.Shift (-d))), s)), dp, sc)
  (* we don't increase the proof term here! *)
  (* fail *)

  and aSolve = function
    | (trivial_, s), dp, cnstr, sc -> begin
        if Assign.solveCnstr cnstr then sc [] else ()
      end
    | (C.UnifyEq (g'_, e1, n_, eqns), s), (C.DProg (g_, dPool) as dp), cnstr, sc
      ->
        let g''_ = append (g'_, g_) in
        let s' = shift (g'_, s) in
        begin if Assign.unifiable (g''_, (n_, s'), (e1, s')) then
          aSolve ((eqns, s), dp, cnstr, sc)
        else ()
        end

  and matchAtom (((I.Root (ha_, s_), s) as ps'), (C.DProg (g_, dPool) as dp), sc)
      =
    let rec matchSig = function
      | [] -> ()
      | (I.Const c as hc_) :: sgn' ->
          let (C.SClause r) = C.sProgLookup (cidFromHead hc_) in
          begin
            Cs_manager.trail (function () ->
                rSolve (ps', (r, I.id), dp, function s_ -> sc (C.Pc c :: s_)));
            matchSig sgn'
          end
      (* trail to undo EVar instantiations *)
      (* return indicates failure *)
    in
    let rec matchDProg = function
      | I.Null, I.Null, _ -> matchSig (Index.lookup (cidFromHead ha_))
      | I.Decl (g_, _), I.Decl (dPool', C.Dec (r, s, ha'_)), k -> begin
          if eqHead (ha_, ha'_) then begin
            Cs_manager.trail (function () ->
                rSolve
                  ( ps',
                    (r, I.comp (s, I.Shift k)),
                    dp,
                    function s_ -> sc (C.Dc k :: s_) ));
            matchDProg (g_, dPool', k + 1)
          end
          else matchDProg (g_, dPool', k + 1)
        end
      | I.Decl (g_, _), I.Decl (dPool', parameter_), k ->
          matchDProg (g_, dPool', k + 1)
      (* dynamic program exhausted, try signature *)
    in
    let rec matchConstraint (solve_fn, try_) =
      let succeeded =
        Cs_manager.trail (function () ->
            begin match solve_fn (g_, I.SClo (s_, s), try_) with
            | Some u_ -> begin
                sc [ C.Csolver u_ ];
                true
              end
            | None -> false
            end)
      in
      begin if succeeded then matchConstraint (solve_fn, try_ + 1) else ()
      end
    in
    begin match I.constStatus (cidFromHead ha_) with
    | I.Constraint (cs, solve_fn) -> matchConstraint (solve_fn, 0)
    | _ -> matchDProg (g_, dPool, 1)
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
  let rec retrieval = function
    | Loop, (g'_, u'_, s'), sc, (asub, answRef), n -> begin
        if T.noAnswers answRef then ()
        else retrieve (n, (g'_, u'_, s'), (asub, answRef), sc)
      end
    | Divergence ((p, s), dp), (g'_, u'_, s'), sc, (asub, answRef), n ->
        matchAtom
          ( (p, s),
            dp,
            function
            | pskeleton -> begin
                match MT.answerCheck (s', answRef, pskeleton) with
                | repeated -> ()
                | new_ -> sc pskeleton
              end )

  let rec tableSize () = MT.tableSize ()
  let rec suspGoalNo () = List.length !suspGoals_

  (*  nextStage () = bool
     Side effect: advances lookup pointers
   *)
  let rec nextStage () =
    let rec resume = function
      | [] -> ()
      | (susp_, s, sc, trail, (asub, answRef), k) :: goals_ -> begin
          Cs_manager.trail (function () ->
              begin
                Unify.resume trail;
                retrieval (susp_, s, sc, (asub, answRef), k)
              end);
          resume goals_
        end
    in
    let sg_ = rev !suspGoals_ in
    begin if MT.updateTable () then begin
      TableParam.stageCtr := !TableParam.stageCtr + 1;
      begin
        resume sg_;
        true
      end
    end
    else false
    end
  (* table changed during previous stage *)
  (* table did not change during previous stage *)

  let rec reset () =
    begin
      suspGoals_ := [];
      begin
        MT.reset ();
        TableParam.stageCtr := 0
      end
    end

  let rec solveQuery ((g, s), (C.DProg (g_, dPool) as dp), sc) =
    !solve_fn_ref ((g, s), dp, sc)
  (* only works when query is atomic -- if query is not atomic,
      then the subordination relation might be extended and strengthening may not be sound *)

  (* local ... *)
  let () = solve_fn_ref := solveQuery
end
(*!  sharing Print.IntSyn = IntSyn' !*)
(*              structure Names : NAMES *)
(*!  sharing Names.IntSyn = IntSyn' !*)
(*! structure Cs_manager : CS_MANAGER !*)
(*!  sharing Cs_manager.IntSyn = IntSyn'!*)
(* functor Tabled *)
(* # 1 "src/opsem/tabled_machine.sml.ml" *)
