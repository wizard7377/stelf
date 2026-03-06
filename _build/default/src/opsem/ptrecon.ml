# 1 "src/opsem/ptrecon.sig.ml"
open! Basis;;
(* Abstract Machine guided by proof skeleton *);;
(* Author: Brigitte Pientks *);;
(* Modified: Jeff Polakow *);;
(* Modified: Frank Pfenning *);;
(* Proof term reconstruction by proof skeleton *);;
module type PTRECON = sig
                      (*! structure IntSyn : INTSYN !*)
                      (*! structure CompSyn : COMPSYN !*)
                      exception Error of string 
                      val
                        solve : (CompSyn.pskeleton *
                                 (CompSyn.goal_ * IntSyn.sub_) *
                                 CompSyn.dProg_ *
                                 ((CompSyn.pskeleton * IntSyn.exp_) -> unit)) ->
                                unit
                      end;;
(* signature PTRECON *);;
# 1 "src/opsem/ptrecon.fun.ml"
open! Index;;
open! Basis;;
(* Abstract Machine execution guided by proof skeleton *);;
(* Author: Brigitte Pientka *);;
(* Modified: Jeff Polakow, Frank Pfenning, Larry Greenfield, Roberto Virga, Brigitte Pientka *);;
(* Proof term reconstruction from proof skeleton *);;
module PtRecon(PtRecon__0: sig
                           (*! structure IntSyn' : INTSYN !*)
                           (*! structure CompSyn' : COMPSYN !*)
                           (*! sharing CompSyn'.IntSyn = IntSyn' !*)
                           module Unify : UNIFY
                           (*! sharing Unify.IntSyn = IntSyn' !*)
                           module Assign : ASSIGN
                           (*! sharing Assign.IntSyn = IntSyn' !*)
                           (*! structure TableParam : TABLEPARAM !*)
                           module MemoTable : MEMOTABLE
                           (*! sharing MemoTable.TableParam = TableParam !*)
                           module Index : INDEX
                           (*! sharing Index.IntSyn = IntSyn' !*)
                           (* CPrint currently unused *)
                           module CPrint : CPRINT
                           (*! sharing CPrint.IntSyn = IntSyn' !*)
                           (*! sharing CPrint.CompSyn = CompSyn' !*)
                           module Names : NAMES
                           end) : PTRECON
  =
  struct
    (*! structure IntSyn = IntSyn' !*);;
    (*! structure CompSyn = CompSyn' !*);;
    (*! structure TableParam = TableParam !*);;
    open!
      struct
        module I = IntSyn;;
        module C = CompSyn;;
        module MT = MemoTable;;
        end;;
    exception Error of string ;;
    let rec cidFromHead = function 
                                   | I.Const a -> a
                                   | I.Def a -> a;;
    let rec eqHead =
      function 
               | (I.Const a, I.Const a') -> a = a'
               | (I.Def a, I.Def a') -> a = a'
               | _ -> false;;
    let rec compose' =
      function 
               | (null_, g_) -> g_
               | (IntSyn.Decl (g_, d_), g'_)
                   -> (IntSyn.Decl (compose' (g_, g'_), d_));;
    let rec shift =
      function 
               | (null_, s) -> s
               | (IntSyn.Decl (g_, d_), s) -> I.dot1 (shift (g_, s));;
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

     Non-determinism within the rules is resolved by oracle
  *);;
    (* solve' (o, (g, s), dp, sc) => ()
     Invariants:
       o = oracle
       dp = (G, dPool) where  G ~ dPool  (context G matches dPool)
       G |- s : G'
       G' |- g  goal
       if  G |- M : g[s]
       then  sc M  is evaluated
     Effects: instantiation of EVars in g, s, and dp
              any effect  sc M  might have
  *);;
    let rec solve' =
      function 
               | (o_, (C.Atom p, s), (C.DProg (g_, dPool) as dp), sc)
                   -> matchAtom (o_, (p, s), dp, sc)
               | (o_, (C.Impl (r, a_, ha_, g), s), C.DProg (g_, dPool), sc)
                   -> let d'_ = (I.Dec (None, (I.EClo (a_, s)))) in begin
                        if ! TableParam.strengthen then
                        begin
                        match MT.memberCtx ((g_, (I.EClo (a_, s))), g_)
                        with 
                             | Some d_
                                 -> let x_ = I.newEVar (g_, (I.EClo (a_, s)))
                                      in solve'
                                         (o_, (g, (I.Dot ((I.Exp x_), s))),
                                          (C.DProg (g_, dPool)),
                                          function 
                                                   | (o_, m_)
                                                       -> sc
                                                          (o_,
                                                           (I.Lam (d'_, m_))))
                                      (* need to reuse label for this assumption .... *)
                             | None
                                 -> solve'
                                    (o_, (g, I.dot1 s),
                                     (C.DProg
                                      ((I.Decl (g_, d'_)),
                                       (I.Decl (dPool, (C.Dec (r, s, ha_)))))),
                                     function 
                                              | (o_, m_)
                                                  -> sc
                                                     (o_, (I.Lam (d'_, m_))))
                        end else
                        solve'
                        (o_, (g, I.dot1 s),
                         (C.DProg
                          ((I.Decl (g_, d'_)),
                           (I.Decl (dPool, (C.Dec (r, s, ha_)))))),
                         function 
                                  | (o_, m_) -> sc (o_, (I.Lam (d'_, m_))))
                        end
                        (*      solve' (O, (g, I.dot1 s), C.DProg (I.Decl(G, D'), I.Decl (dPool, C.Dec (r, s, Ha))),
               (fn (O,M) => sc (O, (I.Lam (D', M)))))*)
               | (o_, (C.All (d_, g), s), C.DProg (g_, dPool), sc)
                   -> let d'_ = Names.decLUName (g_, I.decSub (d_, s))
                        in solve'
                           (o_, (g, I.dot1 s),
                            (C.DProg
                             ((I.Decl (g_, d'_)),
                              (I.Decl (dPool, C.parameter_)))),
                            function 
                                     | (o_, m_) -> sc (o_, (I.Lam (d'_, m_))))
                        (* val D' = I.decSub (D, s) *)
    and rSolve =
      function 
               | (o_, ps', (C.Eq q_, s), C.DProg (g_, dPool), sc) -> begin
                   if Unify.unifiable (g_, (q_, s), ps') then sc (o_, I.nil_)
                   else
                   let _ =
                     begin
                       print "Unification Failed -- SHOULD NEVER HAPPEN!\n";
                       begin
                         print
                         ((Print.expToString (g_, (I.EClo ps'))) ^ " unify ");
                         print
                         ((Print.expToString (g_, (I.EClo (q_, s)))) ^ "\n")
                         end
                       
                       end
                     in ()
                   end
                   (* effect: instantiate EVars *)(* call success continuation *)
               | (o_, ps', (C.Assign (q_, eqns), s),
                  (C.DProg (g_, dPool) as dp), sc)
                   -> begin
                      match Assign.assignable (g_, ps', (q_, s))
                      with 
                           | Some cnstr -> begin
                               if aSolve ((eqns, s), dp, cnstr) then
                               sc (o_, I.nil_) else
                               print
                               "aSolve cnstr not solvable -- SHOULD NEVER HAPPEN\n"
                               end
                           | None
                               -> print
                                  "Clause Head not assignable -- SHOULD NEVER HAPPEN\n"
                      end
               | (o_, ps', (C.And (r, a_, g), s),
                  (C.DProg (g_, dPool) as dp), sc)
                   -> let x_ = I.newEVar (g_, (I.EClo (a_, s)))
                        in rSolve
                           (o_, ps', (r, (I.Dot ((I.Exp x_), s))), dp,
                            function 
                                     | (o_, s_)
                                         -> solve'
                                            (o_, (g, s), dp,
                                             function 
                                                      | (o_, m_)
                                                          -> sc
                                                             (o_,
                                                              (I.App
                                                               (m_, s_)))))
                        (* is this EVar redundant? -fp *)
               | (o_, ps', (C.Exists (I.Dec (_, a_), r), s),
                  (C.DProg (g_, dPool) as dp), sc)
                   -> let x_ = I.newEVar (g_, (I.EClo (a_, s)))
                        in rSolve
                           (o_, ps', (r, (I.Dot ((I.Exp x_), s))), dp,
                            function 
                                     | (o_, s_) -> sc (o_, (I.App (x_, s_))))
               | (o_, ps', (C.Axists (I.ADec (Some x_, d), r), s),
                  (C.DProg (g_, dPool) as dp), sc)
                   -> let x'_ = I.newAVar ()
                        in rSolve
                           (o_, ps',
                            (r,
                             (I.Dot
                              ((I.Exp ((I.EClo (x'_, (I.Shift (- d)))))), s))),
                            dp, sc)
                        (* we don't increase the proof term here! *)(* fail *)
    and aSolve =
      function 
               | ((trivial_, s), dp, cnstr) -> Assign.solveCnstr cnstr
               | ((C.UnifyEq (g'_, e1, n_, eqns), s),
                  (C.DProg (g_, dPool) as dp), cnstr)
                   -> let g''_ = compose' (g'_, g_)
                        in let s' = shift (g'_, s)
                             in (Assign.unifiable (g''_, (n_, s'), (e1, s')))
                                  && (aSolve ((eqns, s), dp, cnstr))
    and matchAtom
      ((ho_ :: o_), ((I.Root (ha_, s_), s) as ps'),
       (C.DProg (g_, dPool) as dp), sc)
      =
      let rec matchSig =
        function 
                 | ([], k)
                     -> raise ((Error " \noracle #Pc does not exist \n"))
                 | (((I.Const c as hc_) :: sgn'), k) -> begin
                     if c = k then
                     let C.SClause r = C.sProgLookup (cidFromHead hc_)
                       in rSolve
                          (o_, ps', (r, I.id), dp,
                           function 
                                    | (o_, s_) -> sc (o_, (I.Root (hc_, s_))))
                     else matchSig (sgn', k) end
                 | (((I.Def d as hc_) :: sgn'), k) -> begin
                     if d = k then
                     let C.SClause r = C.sProgLookup (cidFromHead hc_)
                       in rSolve
                          (o_, ps', (r, I.id), dp,
                           function 
                                    | (o_, s_) -> sc (o_, (I.Root (hc_, s_))))
                     else matchSig (sgn', k) end(* should not happen *)
        in let rec matchDProg =
             function 
                      | (null_, i, k)
                          -> raise
                             ((Error
                               "\n selected dynamic clause number does not exist in current dynamic clause pool!\n"))
                      | (I.Decl (dPool', C.Dec (r, s, ha'_)), 1, k) -> begin
                          if eqHead (ha_, ha'_) then
                          rSolve
                          (o_, ps', (r, I.comp (s, (I.Shift k))), dp,
                           function 
                                    | (o_, s_)
                                        -> sc (o_, (I.Root ((I.BVar k), s_))))
                          else
                          raise
                          ((Error
                            "\n selected dynamic clause does not match current goal!\n"))
                          end (* shouldn't happen *)
                      | (I.Decl (dPool', dc), i, k)
                          -> matchDProg (dPool', i - 1, k)(* dynamic program exhausted -- shouldn't happen *)
             in begin
                match ho_
                with 
                     | C.Pc i -> matchSig (Index.lookup (cidFromHead ha_), i)
                     | C.Dc i -> matchDProg (dPool, i, i)
                     | C.Csolver u_ -> sc (o_, u_)
                end
             (* matchSig [c1,...,cn] = ()
           try each constant ci in turn for solving atomic goal ps', starting
           with c1.
        *)(* matchDProg (dPool, k) = ()
           where k is the index of dPool in global dPool from call to matchAtom.
           Try each local assumption for solving atomic goal ps', starting
           with the most recent one.
        *);;
    (* rsolve (O, (p,s'), (r,s), dp, sc) = ()
     Invariants:
       O = oracle
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
    (* aSolve ((ag, s), dp, sc) = res
     Invariants:
       dp = (G, dPool) where G ~ dPool
       G |- s : G'
       if G |- ag[s] auxgoal
       then sc () is evaluated with return value res
       else res = Fail
     Effects: instantiation of EVars in ag[s], dp and sc () *);;
    (* matchatom (O, (p, s), dp, sc) => ()
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
    let rec solve (o_, (g, s), (C.DProg (g_, dPool) as dp), sc) =
      try solve' (o_, (g, s), dp, sc) with 
                                           | Error msg -> print msg;;
    end;;
(*! sharing Names.IntSyn = IntSyn' !*);;
(*! structure CSManager : CS_MANAGER !*);;
(*! sharing CSManager.IntSyn = IntSyn' !*);;
(* local ... *);;
(* functor PtRecon *);;
# 1 "src/opsem/ptrecon.sml.ml"
