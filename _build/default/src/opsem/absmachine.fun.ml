open! Index;;
open! Basis;;
(* Abstract Machine *);;
(* Author: Iliano Cervesato *);;
(* Modified: Jeff Polakow, Frank Pfenning, Larry Greenfield, Roberto Virga *);;
module AbsMachine(AbsMachine__0: sig
                                 (*! structure IntSyn' : INTSYN !*)
                                 (*! structure CompSyn' : COMPSYN !*)
                                 (*! sharing CompSyn'.IntSyn = IntSyn' !*)
                                 module Unify : UNIFY
                                 (*! sharing Unify.IntSyn = IntSyn' !*)
                                 module Assign : ASSIGN
                                 (*! sharing Assign.IntSyn = IntSyn' !*)
                                 module Index : INDEX
                                 (*! sharing Index.IntSyn = IntSyn' !*)
                                 (* CPrint currently unused *)
                                 module CPrint : CPRINT
                                 (*! sharing CPrint.IntSyn = IntSyn' !*)
                                 (*! sharing CPrint.CompSyn = CompSyn' !*)
                                 module Print : PRINT
                                 (*! sharing Print.IntSyn = IntSyn' !*)
                                 module Names : NAMES
                                 end) : ABSMACHINE
  =
  struct
    (*! structure IntSyn = IntSyn' !*);;
    (*! structure CompSyn = CompSyn' !*);;
    open!
      struct
        module I = IntSyn;;
        module C = CompSyn;;
        let rec cidFromHead = function 
                                       | I.Const a -> a
                                       | I.Def a -> a;;
        let rec eqHead =
          function 
                   | (I.Const a, I.Const a') -> a = a'
                   | (I.Def a, I.Def a') -> a = a'
                   | _ -> false;;
        let rec compose =
          function 
                   | (g_, null_) -> g_
                   | (g_, IntSyn.Decl (g'_, d_))
                       -> (IntSyn.Decl (compose (g_, g'_), d_));;
        let rec shiftSub =
          function 
                   | (null_, s) -> s
                   | (IntSyn.Decl (g_, d_), s) -> I.dot1 (shiftSub (g_, s));;
        let rec raiseType =
          function 
                   | (null_, v_) -> v_
                   | (I.Decl (g_, d_), v_)
                       -> raiseType (g_, (I.Pi ((d_, I.maybe_), v_)));;
        let rec solve =
          function 
                   | ((C.Atom p, s), (C.DProg (g_, dPool) as dp), sc)
                       -> matchAtom ((p, s), dp, sc)
                   | ((C.Impl (r, a_, ha_, g), s), C.DProg (g_, dPool), sc)
                       -> let d'_ = (I.Dec (None, (I.EClo (a_, s))))
                            in (Solve_
                                ((g, I.dot1 s),
                                 (C.DProg
                                  ((I.Decl (g_, d'_)),
                                   (I.Decl (dPool, (C.Dec (r, s, ha_)))))),
                                 function 
                                          | m_ -> sc ((I.Lam (d'_, m_)))))
                   | ((C.All (d_, g), s), C.DProg (g_, dPool), sc)
                       -> let d'_ = Names.decLUName (g_, I.decSub (d_, s))
                            in (Solve_
                                ((g, I.dot1 s),
                                 (C.DProg
                                  ((I.Decl (g_, d'_)),
                                   (I.Decl (dPool, C.parameter_)))),
                                 function 
                                          | m_ -> sc ((I.Lam (d'_, m_)))))
        and rSolve =
          function 
                   | (ps', (C.Eq q_, s), C.DProg (g_, dPool), sc) -> begin
                       if Unify.unifiable (g_, (q_, s), ps') then sc I.nil_
                       else () end
                   | (ps', (C.Assign (q_, eqns), s),
                      (C.DProg (g_, dPool) as dp), sc)
                       -> begin
                          match Assign.assignable (g_, ps', (q_, s))
                          with 
                               | Some cnstr
                                   -> aSolve
                                      ((eqns, s), dp, cnstr,
                                       function 
                                                | () -> sc I.nil_)
                               | None -> ()
                          end
                   | (ps', (C.And (r, a_, g), s),
                      (C.DProg (g_, dPool) as dp), sc)
                       -> let x_ = I.newEVar (g_, (I.EClo (a_, s)))
                            in rSolve
                               (ps', (r, (I.Dot ((I.Exp x_), s))), dp,
                                function 
                                         | s_
                                             -> (Solve_
                                                 ((g, s), dp,
                                                  function 
                                                           | m_
                                                               -> sc
                                                                  ((I.App
                                                                    (m_, s_))))))
                   | (ps', (C.Exists (I.Dec (_, a_), r), s),
                      (C.DProg (g_, dPool) as dp), sc)
                       -> let x_ = I.newEVar (g_, (I.EClo (a_, s)))
                            in rSolve
                               (ps', (r, (I.Dot ((I.Exp x_), s))), dp,
                                function 
                                         | s_ -> sc ((I.App (x_, s_))))
                   | (ps', (C.Axists (I.ADec (_, d), r), s),
                      (C.DProg (g_, dPool) as dp), sc)
                       -> let x'_ = I.newAVar ()
                            in rSolve
                               (ps',
                                (r,
                                 (I.Dot
                                  ((I.Exp ((I.EClo (x'_, (I.Shift (- d)))))),
                                   s))),
                                dp, sc)
        and aSolve =
          function 
                   | ((trivial_, s), dp, cnstr, sc) -> begin
                       if Assign.solveCnstr cnstr then sc () else () end
                   | ((C.UnifyEq (g'_, e1, n_, eqns), s),
                      (C.DProg (g_, dPool) as dp), cnstr, sc)
                       -> let g''_ = compose (g_, g'_)
                            in let s' = shiftSub (g'_, s) in begin
                                 if
                                 Assign.unifiable (g''_, (n_, s'), (e1, s'))
                                 then aSolve ((eqns, s), dp, cnstr, sc) else
                                 () end
        and matchAtom
          (((I.Root (ha_, s_), s) as ps'), (C.DProg (g_, dPool) as dp), sc) =
          let deterministic = C.detTableCheck (cidFromHead ha_)
            in (let exception SucceedOnce of I.spine_ 
                in let rec matchSig =
                     function 
                              | [] -> ()
                              | (hc_ :: sgn')
                                  -> let C.SClause r =
                                       C.sProgLookup (cidFromHead hc_)
                                       in begin
                                            CSManager.trail
                                            (function 
                                                      | ()
                                                          -> rSolve
                                                             (ps', (r, I.id),
                                                              dp,
                                                              function 
                                                                    | s_
                                                                    -> sc
                                                                    ((I.Root
                                                                    (hc_, s_)))));
                                            matchSig sgn'
                                            end
                     in let rec matchSigDet =
                          function 
                                   | [] -> ()
                                   | (hc_ :: sgn')
                                       -> let C.SClause r =
                                            C.sProgLookup (cidFromHead hc_)
                                            in try begin
                                                     CSManager.trail
                                                     (function 
                                                               | ()
                                                                   -> 
                                                                   rSolve
                                                                   (ps',
                                                                    (r, I.id),
                                                                    dp,
                                                                    function 
                                                                    | s_
                                                                    -> raise
                                                                    ((SucceedOnce
                                                                    s_))));
                                                     matchSigDet sgn'
                                                     end
                                               with 
                                                    | SucceedOnce s_
                                                        -> sc
                                                           ((I.Root
                                                             (hc_, s_)))
                          in let rec matchDProg =
                               function 
                                        | (null_, _) -> begin
                                            if deterministic then
                                            matchSigDet
                                            (Index.lookup (cidFromHead ha_))
                                            else
                                            matchSig
                                            (Index.lookup (cidFromHead ha_))
                                            end
                                        | (I.Decl
                                           (dPool', C.Dec (r, s, ha'_)), k)
                                            -> begin
                                            if eqHead (ha_, ha'_) then begin
                                            if deterministic then
                                            try begin
                                                  CSManager.trail
                                                  (function 
                                                            | ()
                                                                -> rSolve
                                                                   (ps',
                                                                    (r,
                                                                    I.comp
                                                                    (s,
                                                                    (I.Shift
                                                                    k))), dp,
                                                                    function 
                                                                    | s_
                                                                    -> raise
                                                                    ((SucceedOnce
                                                                    s_))));
                                                  matchDProg (dPool', k + 1)
                                                  end
                                            with 
                                                 | SucceedOnce s_
                                                     -> sc
                                                        ((I.Root
                                                          ((I.BVar k), s_)))
                                            else
                                            begin
                                              CSManager.trail
                                              (function 
                                                        | ()
                                                            -> rSolve
                                                               (ps',
                                                                (r,
                                                                 I.comp
                                                                 (s,
                                                                  (I.Shift k))),
                                                                dp,
                                                                function 
                                                                    | s_
                                                                    -> sc
                                                                    ((I.Root
                                                                    ((I.BVar
                                                                    k), s_)))));
                                              matchDProg (dPool', k + 1)
                                              end
                                            end else
                                            matchDProg (dPool', k + 1) end
                                        | (I.Decl (dPool', parameter_), k)
                                            -> matchDProg (dPool', k + 1)
                               in let rec matchConstraint (cnstrSolve, try_)
                                    =
                                    let succeeded =
                                      CSManager.trail
                                      (function 
                                                | ()
                                                    -> begin
                                                       match cnstrSolve
                                                             (g_,
                                                              (I.SClo
                                                               (s_, s)),
                                                              try_)
                                                       with 
                                                            | Some u_
                                                                -> begin
                                                                    sc u_;
                                                                    true
                                                                    end
                                                            | None -> false
                                                       end)
                                      in begin
                                      if succeeded then
                                      matchConstraint (cnstrSolve, try_ + 1)
                                      else () end
                                    in begin
                                       match I.constStatus (cidFromHead ha_)
                                       with 
                                            | I.Constraint (cs, cnstrSolve)
                                                -> matchConstraint
                                                   (cnstrSolve, 0)
                                            | _ -> matchDProg (dPool, 1)
                                       end);;
        end;;
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
  *);;
    (* Wed Mar 13 10:27:00 2002 -bp  *);;
    (* should probably go to intsyn.fun *);;
    (* solve ((g, s), dp, sc) = ()
     Invariants:
       dp = (G, dPool) where  G ~ dPool  (context G matches dPool)
       G |- s : G'
       G' |- g  goal
       if  G |- M : g[s]
       then  sc M  is evaluated

     Effects: instantiation of EVars in g, s, and dp
              any effect  sc M  might have
  *);;
    (*      val D' = I.decSub (D, s) *);;
    (* rSolve ((p,s'), (r,s), dp, sc) = ()
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
  *);;
    (* effect: instantiate EVars *);;
    (* call success continuation *);;
    (* fail *);;
    (* is this EVar redundant? -fp *);;
    (* same effect as s^-1 *);;
    (* we don't increase the proof term here! *);;
    (* aSolve ((ag, s), dp, sc) = ()
     Invariants:
       dp = (G, dPool) where G ~ dPool
       G |- s : G'
       if G |- ag[s] auxgoal
       then sc () is evaluated
     Effects: instantiation of EVars in ag[s], dp and sc () *);;
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
  *);;
    (* matchSig [c1,...,cn] = ()
           try each constant ci in turn for solving atomic goal ps', starting
           with c1.

           #succeeds >= 1 (succeeds at least once)
        *);;
    (* return unit on failure *);;
    (* trail to undo EVar instantiations *);;
    (* matchSigDet [c1,...,cn] = ()
           try each constant ci in turn for solving atomic goal ps', starting
           with c1.

           succeeds exactly once (#succeeds = 1)
        *);;
    (* return unit on failure *);;
    (* trail to undo EVar instantiations *);;
    (* matchDProg (dPool, k) = ()
           where k is the index of dPool in global dPool from call to matchAtom.
           Try each local assumption for solving atomic goal ps', starting
           with the most recent one.
        *);;
    (* dynamic program exhausted, try signature *);;
    (* #succeeds = 1 *);;
    (* trail to undo EVar instantiations *);;
    (* #succeeds >= 1 -- allows backtracking *);;
    (* trail to undo EVar instantiations *);;
    let Solve_ = Solve_;;
    end;;
(*! sharing Names.IntSyn = IntSyn' !*);;
(*! structure CSManager : CS_MANAGER !*);;
(*! sharing CSManager.IntSyn = IntSyn' !*);;
(* local ... *);;
(* functor AbsMachine *);;