(* # 1 "src/opsem/tmachine.sig.ml" *)

(* # 1 "src/opsem/tmachine.fun.ml" *)
open! Index
open! Trace
open! Absmachine
open! Basis

(* Abstract Machine for Tracing *)
(* Author: Frank Pfenning *)
(* Modified: Jeff Polakow, Frank Pfenning, Larry Greenfield, Roberto Virga *)
module TMachine (TMachine__0 : sig
  (*! structure IntSyn' : INTSYN !*)
  (*! structure CompSyn' : COMPSYN !*)
  (*! sharing CompSyn'.IntSyn = IntSyn' !*)
  module Unify : UNIFY

  (*! sharing Unify.IntSyn = IntSyn' !*)
  module Assign : ASSIGN

  (*! sharing Assign.IntSyn = IntSyn' !*)
  module Index : INDEX

  (*! sharing Index.IntSyn = IntSyn' !*)
  module CPrint : Cprint.CPRINT

  (*! sharing CPrint.IntSyn = IntSyn' !*)
  (*! sharing CPrint.CompSyn = CompSyn' !*)
  module Names : NAMES

  (*! sharing Names.IntSyn = IntSyn' !*)
  (*! structure Cs_manager : CS_MANAGER !*)
  (*! sharing Cs_manager.IntSyn = IntSyn' !*)
  module Trace : TRACE
end) : ABSMACHINE = struct
  open TMachine__0

  (*! structure IntSyn = IntSyn' !*)
  (*! structure CompSyn = CompSyn' !*)
  open! struct
    module I = IntSyn
    module C = CompSyn
    module T = Trace
    module N = Names

    let cidFromHead = function I.Const a -> a | I.Def a -> a

    let rec eqHead = function
      | I.Const a, I.Const a' -> a = a'
      | I.Def a, I.Def a' -> a = a'
      | _ -> false

    let rec compose = function
      | g_, I.Null -> g_
      | g_, IntSyn.Decl (g'_, d_) -> IntSyn.Decl (compose (g_, g'_), d_)

    let rec shiftSub = function
      | I.Null, s -> s
      | IntSyn.Decl (g_, d_), s -> I.dot1 (shiftSub (g_, s))

    let rec subgoalNum = function
      | I.Nil -> 1
      | I.App (u_, s_) -> 1 + subgoalNum s_

    let rec goalToType = function
      | C.All (d_, g), s ->
          I.Pi ((I.decSub (d_, s), I.Maybe), goalToType (g, I.dot1 s))
      | C.Impl (_, a_, _, g), s ->
          I.Pi ((I.Dec (None, I.EClo (a_, s)), I.No), goalToType (g, I.dot1 s))
      | C.Atom p, s -> I.EClo (p, s)

    let rec solve' = function
      | (C.Atom p, s), (C.DProg (g_, dPool) as dp), sc ->
          matchAtom ((p, s), dp, sc)
      | (C.Impl (r, a_, ha_, g), s), C.DProg (g_, dPool), sc ->
          let (I.Dec (Some x, _) as d'_) =
            N.decUName (g_, I.Dec (None, I.EClo (a_, s)))
          in
          let _ = T.signal (g_, T.IntroHyp (ha_, d'_)) in
          solve'
            ( (g, I.dot1 s),
              C.DProg (I.Decl (g_, d'_), I.Decl (dPool, C.Dec (r, s, ha_))),
              function
              | m_ -> begin
                  T.signal (g_, T.DischargeHyp (ha_, d'_));
                  sc (I.Lam (d'_, m_))
                end )
      | (C.All (d_, g), s), C.DProg (g_, dPool), sc ->
          let (I.Dec (Some x, v_) as d'_) = N.decUName (g_, I.decSub (d_, s)) in
          let ha_ = I.targetHead v_ in
          let _ = T.signal (g_, T.IntroParm (ha_, d'_)) in
          solve'
            ( (g, I.dot1 s),
              C.DProg (I.Decl (g_, d'_), I.Decl (dPool, C.Parameter)),
              function
              | m_ -> begin
                  T.signal (g_, T.DischargeParm (ha_, d'_));
                  sc (I.Lam (d'_, m_))
                end )

    and rSolve = function
      | ps', (C.Eq q_, s), C.DProg (g_, dPool), hcHa_, sc -> begin
          T.signal
            (g_, T.Unify (hcHa_, I.EClo (q_, s), I.EClo (fst ps', snd ps')));
          begin match Unify.unifiable' (g_, (q_, s), ps') with
          | None -> begin
              T.signal (g_, T.Resolved (fst hcHa_, snd hcHa_));
              begin
                sc I.Nil;
                true
              end
            end
          | Some msg -> begin
              T.signal (g_, T.FailUnify (hcHa_, msg));
              false
            end
          end
        end
      | ps', (C.Assign (q_, eqns), s), (C.DProg (g_, dPool) as dp), hcHa_, sc ->
        begin
          match Assign.assignable (g_, ps', (q_, s)) with
          | Some cnstr ->
              aSolve ((eqns, s), dp, hcHa_, cnstr, function () -> sc I.Nil)
          | None -> false
        end
      | ps', (C.And (r, a_, g), s), (C.DProg (g_, dPool) as dp), hcHa_, sc ->
          let x_ = I.newEVar (g_, I.EClo (a_, s)) in
          rSolve
            ( ps',
              (r, I.Dot (I.Exp x_, s)),
              dp,
              hcHa_,
              function
              | s_ -> begin
                  T.signal
                    (g_, T.Subgoal (hcHa_, function () -> subgoalNum s_));
                  solve' ((g, s), dp, function m_ -> sc (I.App (m_, s_)))
                end )
      | ( ps',
          (C.Exists (I.Dec (_, a_), r), s),
          (C.DProg (g_, dPool) as dp),
          hcHa_,
          sc ) ->
          let x_ = I.newEVar (g_, I.EClo (a_, s)) in
          rSolve
            ( ps',
              (r, I.Dot (I.Exp x_, s)),
              dp,
              hcHa_,
              function s_ -> sc (I.App (x_, s_)) )
      | ( ps',
          (C.Axists (I.ADec (_, d), r), s),
          (C.DProg (g_, dPool) as dp),
          hcHa_,
          sc ) ->
          let x_ = I.newAVar () in
          rSolve
            ( ps',
              (r, I.Dot (I.Exp (I.EClo (x_, I.Shift (-d))), s)),
              dp,
              hcHa_,
              sc )

    and aSolve = function
      | (trivial_, s), (C.DProg (g_, dPool) as dp), hcHa_, cnstr, sc -> begin
          if Assign.solveCnstr cnstr then begin
            T.signal (g_, T.Resolved (fst hcHa_, snd hcHa_));
            begin
              sc ();
              true
            end
          end
          else false
        end
      | ( (C.UnifyEq (g'_, e1, n_, eqns), s),
          (C.DProg (g_, dPool) as dp),
          hcHa_,
          cnstr,
          sc ) ->
          let g''_ = compose (g_, g'_) in
          let s' = shiftSub (g'_, s) in
          begin if Assign.unifiable (g''_, (n_, s'), (e1, s')) then
            aSolve ((eqns, s), dp, hcHa_, cnstr, sc)
          else false
          end

    and matchAtom
        (((I.Root (ha_, s_), s) as ps'), (C.DProg (g_, dPool) as dp), sc) =
      let tag = T.tagGoal () in
      let _ =
        T.signal (g_, T.SolveGoal (tag, ha_, I.EClo (fst ps', snd ps')))
      in
      let deterministic = C.detTableCheck (cidFromHead ha_) in
      let exception SucceedOnce of I.spine in
      let rec matchSig = function
        | [] -> begin
            T.signal (g_, T.FailGoal (tag, ha_, I.EClo (fst ps', snd ps')));
            ()
          end
        | hc_ :: sgn' ->
            let (C.SClause r) = C.sProgLookup (cidFromHead hc_) in
            begin
              begin if
                Cs_manager.trail (function () ->
                    rSolve
                      ( ps',
                        (r, I.id),
                        dp,
                        (hc_, ha_),
                        function
                        | s_ -> begin
                            T.signal
                              ( g_,
                                T.SucceedGoal
                                  (tag, (hc_, ha_), I.EClo (fst ps', snd ps'))
                              );
                            sc (I.Root (hc_, s_))
                          end ))
              then begin
                T.signal
                  (g_, T.RetryGoal (tag, (hc_, ha_), I.EClo (fst ps', snd ps')));
                ()
              end
              else ()
              end;
              matchSig sgn'
            end
      in
      let rec matchSigDet = function
        | [] -> begin
            T.signal (g_, T.FailGoal (tag, ha_, I.EClo (fst ps', snd ps')));
            ()
          end
        | hc_ :: sgn' -> (
            let (C.SClause r) = C.sProgLookup (cidFromHead hc_) in
            try
              begin
                begin if
                  Cs_manager.trail (function () ->
                      rSolve
                        ( ps',
                          (r, I.id),
                          dp,
                          (hc_, ha_),
                          function
                          | s_ -> begin
                              T.signal
                                ( g_,
                                  T.SucceedGoal
                                    (tag, (hc_, ha_), I.EClo (fst ps', snd ps'))
                                );
                              raise (SucceedOnce s_)
                            end ))
                then begin
                  T.signal
                    ( g_,
                      T.RetryGoal (tag, (hc_, ha_), I.EClo (fst ps', snd ps'))
                    );
                  ()
                end
                else ()
                end;
                matchSigDet sgn'
              end
            with SucceedOnce s_ ->
              begin
                T.signal
                  (g_, T.CommitGoal (tag, (hc_, ha_), I.EClo (fst ps', snd ps')));
                sc (I.Root (hc_, s_))
              end)
      in
      let rec matchDProg = function
        | I.Null, _ -> begin
            if deterministic then matchSigDet (Index.lookup (cidFromHead ha_))
            else matchSig (Index.lookup (cidFromHead ha_))
          end
        | I.Decl (dPool', C.Dec (r, s, ha'_)), k -> begin
            if eqHead (ha_, ha'_) then begin
              if deterministic then
                try
                  begin
                    begin if
                      Cs_manager.trail (function () ->
                          rSolve
                            ( ps',
                              (r, I.comp (s, I.Shift k)),
                              dp,
                              (I.BVar k, ha_),
                              function
                              | s_ -> begin
                                  T.signal
                                    ( g_,
                                      T.SucceedGoal
                                        ( tag,
                                          (I.BVar k, ha_),
                                          I.EClo (fst ps', snd ps') ) );
                                  raise (SucceedOnce s_)
                                end ))
                    then begin
                      T.signal
                        ( g_,
                          T.RetryGoal
                            (tag, (I.BVar k, ha_), I.EClo (fst ps', snd ps')) );
                      ()
                    end
                    else ()
                    end;
                    matchDProg (dPool', k + 1)
                  end
                with SucceedOnce s_ ->
                  begin
                    T.signal
                      ( g_,
                        T.CommitGoal
                          (tag, (I.BVar k, ha_), I.EClo (fst ps', snd ps')) );
                    sc (I.Root (I.BVar k, s_))
                  end
              else begin
                begin if
                  Cs_manager.trail (function () ->
                      rSolve
                        ( ps',
                          (r, I.comp (s, I.Shift k)),
                          dp,
                          (I.BVar k, ha_),
                          function
                          | s_ -> begin
                              T.signal
                                ( g_,
                                  T.SucceedGoal
                                    ( tag,
                                      (I.BVar k, ha_),
                                      I.EClo (fst ps', snd ps') ) );
                              sc (I.Root (I.BVar k, s_))
                            end ))
                then begin
                  T.signal
                    ( g_,
                      T.RetryGoal
                        (tag, (I.BVar k, ha_), I.EClo (fst ps', snd ps')) );
                  ()
                end
                else ()
                end;
                matchDProg (dPool', k + 1)
              end
            end
            else matchDProg (dPool', k + 1)
          end
        | I.Decl (dPool', parameter_), k -> matchDProg (dPool', k + 1)
      in
      let rec matchConstraint (cnstrSolve, try_) =
        let succeeded =
          Cs_manager.trail (function () ->
              begin match cnstrSolve (g_, I.SClo (s_, s), try_) with
              | Some u_ -> begin
                  sc u_;
                  true
                end
              | None -> false
              end)
        in
        begin if succeeded then matchConstraint (cnstrSolve, try_ + 1) else ()
        end
      in
      begin match I.constStatus (cidFromHead ha_) with
      | I.Constraint (cs, cnstrSolve) -> matchConstraint (cnstrSolve, 0)
      | _ -> matchDProg (dPool, 1)
      end
  end

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
  (* Wed Mar 13 10:27:00 2002 -bp  *)
  (* should probably go to intsyn.fun *)
  (* currently unused *)
  (* solve' ((g, s), dp, sc) = ()
     Invariants:
       dp = (G, dPool) where  G ~ dPool  (context G matches dPool)
       G |- s : G'
       G' |- g  goal
       if  G |- M : g[s]
       then  sc M  is evaluated to

     Effects: instantiation of EVars in g, s, and dp
              any effect  sc M  might have
  *)
  (* rSolve' ((p,s'), (r,s), dp, (Hc, Ha), sc) = T
     Invariants:
       dp = (G, dPool) where G ~ dPool
       G |- s : G'
       G' |- r  resgoal
       G |- s' : G''
       G'' |- p : H @ S' (mod whnf)
       if G |- S : r[s]
       then sc S is evaluated
       Hc is the clause which generated this residual goal
       Ha is the target family of p and r (which must be equal)
     Effects: instantiation of EVars in p[s'], r[s], and dp
              any effect  sc S  might have
  *)
  (* effect: instantiate EVars *)
  (* call success continuation *)
  (* deep backtracking *)
  (* shallow backtracking *)
  (* Do not signal unification events for optimized clauses *)
  (* Optimized clause heads lead to unprintable substitutions *)
  (* T.signal (G, T.Unify (HcHa, I.EClo (Q, s), I.EClo (fst ps', snd ps'))); *)
  (* T.signal (G, T.FailUnify (HcHa, ""Assignment failed"")); *)
  (* is this EVar redundant? -fp *)
  (* we don't increase the proof term here! *)
  (* aSolve ((ag, s), dp, HcHa, sc) = T
     Invariants:
       dp = (G, dPool) where G ~ dPool
       G |- s : G'
       if G |- ag[s] auxgoal
       then sc () is evaluated

     Effects: instantiation of EVars in ag[s], dp and sc () *)
  (* T.signal (G, T.FailUnify (HcHa, ""Dynamic residual equations failed"")); *)
  (* T.signal (G, T.FailUnify (HcHa, ""Static residual equations failed"")); *)
  (* matchatom ((p, s), dp, sc) = res
     Invariants:
       dp = (G, dPool) where G ~ dPool
       G |- s : G'
       G' |- p : type, p = H @ S mod whnf
       if G |- M :: p[s]
       then sc M is evaluated with return value res
       else res = False
     Effects: instantiation of EVars in p[s] and dp
              any effect  sc M  might have

     This first tries the local assumptions in dp then
     the static signature.
  *)
  (* matchSig [c1,...,cn] = ()
           try each constant ci in turn for solving atomic goal ps', starting
           with c1.

           #succeeds >= 1 (succeeds at least once)
        *)
  (* return on failure *)
  (* trail to undo EVar instantiations *)
  (* deep backtracking *)
  (* shallow backtracking *)
  (* matchSigDet [c1,...,cn] = ()
           try each constant ci in turn for solving atomic goal ps', starting
           with c1. -- succeeds exactly once

           succeeds exactly once (#succeeds = 1)
        *)
  (* return on failure *)
  (* trail to undo EVar instantiations *)
  (* deep backtracking *)
  (* shallow backtracking *)
  (* matchDProg (dPool, k) = ()
           where k is the index of dPool in global dPool from call to matchAtom.
           Try each local assumption for solving atomic goal ps', starting
           with the most recent one.
        *)
  (* dynamic program exhausted, try signature *)
  (* #succeeds = 1 *)
  (* trail to undo EVar instantiations *)
  (* deep backtracking *)
  (* shallow backtracking *)
  (* #succeeds >= 1 -- allows backtracking *)
  (* deep backtracking *)
  (* shallow backtracking *)
  let rec solve (gs, dp, sc) =
    begin
      T.init ();
      solve' (gs, dp, sc)
    end
end
(*! sharing Trace.IntSyn = IntSyn' !*)
(* local ... *)
(* functor TMachine *)

(* # 1 "src/opsem/tmachine.sml.ml" *)
