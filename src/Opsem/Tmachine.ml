open! Intsyn.Lambda_
open! Names.Names_
open! Index.Index_
open! Solvers.Solvers_
open! Compile
open! CompSyn
open! Assign

(* # 1 "src/opsem/Tmachine.sig.ml" *)

(* # 1 "src/opsem/Tmachine.fun.ml" *)
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
  (*! structure CsManager : CS_MANAGER !*)
  (*! sharing CsManager.IntSyn = IntSyn' !*)
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

    let eqHead = function
      | I.Const a, I.Const a' -> a = a'
      | I.Def a, I.Def a' -> a = a'
      | _ -> false

    let rec compose (g, a) = match a with
      | I.Null -> g
      | IntSyn.Decl (g', d) -> IntSyn.Decl (compose (g, g'), d)

    let rec shiftSub (a, s) = match a with
      | I.Null -> s
      | IntSyn.Decl (g, d) -> I.dot1 (shiftSub (g, s))

    let rec subgoalNum = function
      | I.Nil -> 1
      | I.App (u, s) -> 1 + subgoalNum s

    let rec goalToType (a, s) = match a with
      | C.All (d, g) ->
          I.Pi ((I.decSub d s, I.Maybe), goalToType (g, I.dot1 s))
      | C.Impl (_, a, _, g) ->
          I.Pi ((I.Dec (None, I.EClo (a, s)), I.No), goalToType (g, I.dot1 s))
      | C.Atom p -> I.EClo (p, s)

    let rec solve' (a, b, sc) = match a, b with
      | (C.Atom p, s), (C.DProg (g, dPool) as dp) ->
          matchAtom ((p, s), dp, sc)
      | (C.Impl (r, a, ha, g), s), C.DProg (g_, dPool) ->
          let (I.Dec (Some x, _) as d') =
            N.decUName g_ (I.Dec (None, I.EClo (a, s)))
          in
          ignore (T.signal g_ (T.IntroHyp (ha, d')));
          solve'
            ( (g, I.dot1 s),
              C.DProg (I.Decl (g_, d'), I.Decl (dPool, C.Dec (r, s, ha))),
              function
              | m -> begin
                  T.signal g_ (T.DischargeHyp (ha, d'));
                  sc (I.Lam (d', m))
                end )
      | (C.All (d, g), s), C.DProg (g_, dPool) ->
          let (I.Dec (Some x, v) as d') = N.decUName g_ (I.decSub d s) in
          let ha = I.targetHead v in
          ignore (T.signal g_ (T.IntroParm (ha, d')));
          solve'
            ( (g, I.dot1 s),
              C.DProg (I.Decl (g_, d'), I.Decl (dPool, C.Parameter)),
              function
              | m -> begin
                  T.signal g_ (T.DischargeParm (ha, d'));
                  sc (I.Lam (d', m))
                end )

    and rSolve (ps', a, b, hcHa, sc) = match a, b with
      | (C.Eq q, s), C.DProg (g, dPool) -> begin
          T.signal
            g (T.Unify (hcHa, I.EClo (q, s), I.EClo (fst ps', snd ps')));
          begin match Unify.unifiable' g (q, s) ps' with
          | None -> begin
              T.signal g (T.Resolved (fst hcHa, snd hcHa));
              begin
                sc I.Nil;
                true
              end
            end
          | Some msg -> begin
              T.signal g (T.FailUnify (hcHa, msg));
              false
            end
          end
        end
      | (C.Assign (q, eqns), s), (C.DProg (g, dPool) as dp) ->
          begin match Assign.assignable g ps' (q, s) with
          | Some cnstr ->
              aSolve ((eqns, s), dp, hcHa, cnstr, function () -> sc I.Nil)
          | None -> false
          end
      | (C.And (r, a, g), s), (C.DProg (g_, dPool) as dp) ->
          let x = I.newEVar g_ (I.EClo (a, s)) in
          rSolve
            ( ps',
              (r, I.Dot (I.Exp x, s)),
              dp,
              hcHa,
              function
              | s_ -> begin
                  T.signal g_ (T.Subgoal (hcHa, function () -> subgoalNum s_));
                  solve' ((g, s), dp, function m -> sc (I.App (m, s_)))
                end )
      | (C.Exists (I.Dec (_, a), r), s), (C.DProg (g, dPool) as dp) ->
          let x = I.newEVar g (I.EClo (a, s)) in
          rSolve
            ( ps',
              (r, I.Dot (I.Exp x, s)),
              dp,
              hcHa,
              function s -> sc (I.App (x, s)) )
      | (C.Axists (I.ADec (_, d), r), s), (C.DProg (g, dPool) as dp) ->
          let x = I.newAVar () in
          rSolve
            ( ps',
              (r, I.Dot (I.Exp (I.EClo (x, I.Shift (-d))), s)),
              dp,
              hcHa,
              sc )

    and aSolve (a, b, hcHa, cnstr, sc) = match a, b with
      | (trivial, s), (C.DProg (g, dPool) as dp) ->
          begin if Assign.solveCnstr cnstr then begin
            T.signal g (T.Resolved (fst hcHa, snd hcHa));
            begin
              sc ();
              true
            end
          end
          else false
          end
      | (C.UnifyEq (g', e1, n, eqns), s), (C.DProg (g, dPool) as dp) ->
          let g'' = compose (g, g') in
          let s' = shiftSub (g', s) in
          begin if Assign.unifiable g'' (n, s') (e1, s') then
            aSolve ((eqns, s), dp, hcHa, cnstr, sc)
          else false
          end

    and matchAtom
        (((I.Root (ha, s_), s) as ps'), (C.DProg (g, dPool) as dp), sc) =
      let tag = T.tagGoal () in
      ignore (T.signal g (T.SolveGoal (tag, ha, I.EClo (fst ps', snd ps'))));
      let deterministic = C.detTableCheck (cidFromHead ha) in
      let exception SucceedOnce of I.spine in
      let rec matchSig = function
        | [] -> begin
            T.signal g (T.FailGoal (tag, ha, I.EClo (fst ps', snd ps')));
            ()
          end
        | hc :: sgn' ->
            let (C.SClause r) = C.sProgLookup (cidFromHead hc) in
            begin if
              CsManager.trail (function () ->
                  rSolve
                    ( ps',
                      (r, I.id),
                      dp,
                      (hc, ha),
                      function
                      | s -> begin
                          T.signal
                            g (T.SucceedGoal
                                (tag, (hc, ha), I.EClo (fst ps', snd ps')));
                          sc (I.Root (hc, s))
                        end ))
            then begin
              T.signal
                g (T.RetryGoal (tag, (hc, ha), I.EClo (fst ps', snd ps')));
              ()
            end
            else ()
            end;
            matchSig sgn'
      in
      let rec matchSigDet = function
        | [] -> begin
            T.signal g (T.FailGoal (tag, ha, I.EClo (fst ps', snd ps')));
            ()
          end
        | hc :: sgn' -> (
            let (C.SClause r) = C.sProgLookup (cidFromHead hc) in
            try
              begin
                begin if
                  CsManager.trail (function () ->
                      rSolve
                        ( ps',
                          (r, I.id),
                          dp,
                          (hc, ha),
                          function
                          | s -> begin
                              T.signal
                                g (T.SucceedGoal
                                    (tag, (hc, ha), I.EClo (fst ps', snd ps')));
                              raise (SucceedOnce s)
                            end ))
                then begin
                  T.signal
                    g (T.RetryGoal (tag, (hc, ha), I.EClo (fst ps', snd ps')));
                  ()
                end
                else ()
                end;
                matchSigDet sgn'
              end
            with SucceedOnce s ->
              begin
                T.signal
                  g (T.CommitGoal (tag, (hc, ha), I.EClo (fst ps', snd ps')));
                sc (I.Root (hc, s))
              end)
      in
      let rec matchDProg (a, k) = match a with
        | I.Null ->
            begin if deterministic then
              matchSigDet (Index.lookup (cidFromHead ha))
            else matchSig (Index.lookup (cidFromHead ha))
            end
        | I.Decl (dPool', C.Dec (r, s, ha')) ->
            begin if eqHead (ha, ha') then
              begin if deterministic then
                try
                  begin
                    begin if
                      CsManager.trail (function () ->
                          rSolve
                            ( ps',
                              (r, I.comp s (I.Shift k)),
                              dp,
                              (I.BVar k, ha),
                              function
                              | s -> begin
                                  T.signal
                                    g (T.SucceedGoal
                                        ( tag,
                                          (I.BVar k, ha),
                                          I.EClo (fst ps', snd ps') ));
                                  raise (SucceedOnce s)
                                end ))
                    then begin
                      T.signal
                        g (T.RetryGoal
                            (tag, (I.BVar k, ha), I.EClo (fst ps', snd ps')));
                      ()
                    end
                    else ()
                    end;
                    matchDProg (dPool', k + 1)
                  end
                with SucceedOnce s ->
                  begin
                    T.signal
                      g (T.CommitGoal
                          (tag, (I.BVar k, ha), I.EClo (fst ps', snd ps')));
                    sc (I.Root (I.BVar k, s))
                  end
              else begin
                begin if
                  CsManager.trail (function () ->
                      rSolve
                        ( ps',
                          (r, I.comp s (I.Shift k)),
                          dp,
                          (I.BVar k, ha),
                          function
                          | s -> begin
                              T.signal
                                g (T.SucceedGoal
                                    ( tag,
                                      (I.BVar k, ha),
                                      I.EClo (fst ps', snd ps') ));
                              sc (I.Root (I.BVar k, s))
                            end ))
                then begin
                  T.signal
                    g (T.RetryGoal
                        (tag, (I.BVar k, ha), I.EClo (fst ps', snd ps')));
                  ()
                end
                else ()
                end;
                matchDProg (dPool', k + 1)
              end
              end
            else matchDProg (dPool', k + 1)
            end
        | I.Decl (dPool', parameter) -> matchDProg (dPool', k + 1)
      in
      let rec matchConstraint (cnstrSolve, try_) =
        let succeeded =
          CsManager.trail (function () ->
              begin match cnstrSolve (g, I.SClo (s_, s), try_) with
              | Some u -> begin
                  sc u;
                  true
                end
              | None -> false
              end)
        in
        begin if succeeded then matchConstraint (cnstrSolve, try_ + 1) else ()
        end
      in
      begin match I.constStatus (cidFromHead ha) with
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
  (* should probably go to Intsyn.fun *)
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
  let solve g s dp sc =
    begin
      T.init ();
      solve' ((g, s), dp, sc)
    end
end
(*! sharing Trace.IntSyn = IntSyn' !*)
(* local ... *)
(* functor TMachine *)

(* # 1 "src/opsem/Tmachine.sml.ml" *)
