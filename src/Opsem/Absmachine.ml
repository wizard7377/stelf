open! Intsyn.Lambda_
open! Names.Names_
open! Print.Print_
open! Index.Index_
open! Solvers.Solvers_
open! Compile
open! CompSyn
open! Assign

(* # 1 "src/opsem/Absmachine.sig.ml" *)

(* Abstract Machine *)
(* Author: Iliano Cervesato *)
(* Modified: Jeff Polakow *)
(* Modified: Frank Pfenning *)
include ABSMACHINE
(* signature ABSMACHINE *)

(* # 1 "src/opsem/Absmachine.fun.ml" *)
open! Basis

(* Abstract Machine *)
(* Author: Iliano Cervesato *)
(* Modified: Jeff Polakow, Frank Pfenning, Larry Greenfield, Roberto Virga *)
module AbsMachine (AbsMachine__0 : sig
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
  module CPrint : Cprint.CPRINT

  (*! sharing CPrint.IntSyn = IntSyn' !*)
  (*! sharing CPrint.CompSyn = CompSyn' !*)
  module Print : PRINT

  (*! sharing Print.IntSyn = IntSyn' !*)
  module Names : NAMES
end) : ABSMACHINE = struct
  open AbsMachine__0

  (*! structure IntSyn = IntSyn' !*)
  (*! structure CompSyn = CompSyn' !*)
  open! struct
    module I = IntSyn
    module C = CompSyn

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

    let rec raiseType a1 b1 = match a1, b1 with
      | I.Null, v -> v
      | I.Decl (g, d), v -> raiseType g (I.Pi ((d, I.Maybe), v))

    let rec solve a1 a2 b2 c2 = match (a1, a2), b2, c2 with
      | (C.Atom p, s), (C.DProg (g, dPool) as dp), sc ->
          matchAtom ((p, s), dp, sc)
      | (C.Impl (r, a, ha, g), s), C.DProg (g_, dPool), sc ->
          let d' = I.Dec (None, I.EClo (a, s)) in
          solve
            g (I.dot1 s) (C.DProg (I.Decl (g_, d'), I.Decl (dPool, C.Dec (r, s, ha)))) (function m -> sc (I.Lam (d', m)))
      | (C.All (d, g), s), C.DProg (g_, dPool), sc ->
          let d' = Names.decLUName g_ (I.decSub d s) in
          solve
            g (I.dot1 s) (C.DProg (I.Decl (g_, d'), I.Decl (dPool, C.Parameter))) (function m -> sc (I.Lam (d', m)))

    and rSolve (ps', a, b, sc) = match a, b with
      | (C.Eq q, s), C.DProg (g, dPool) ->
          begin if Unify.unifiable g (q, s) ps' then sc I.Nil else ()
          end
      | (C.Assign (q, eqns), s), (C.DProg (g, dPool) as dp) ->
          begin match Assign.assignable g ps' (q, s) with
          | Some cnstr ->
              aSolve ((eqns, s), dp, cnstr, function () -> sc I.Nil)
          | None -> ()
          end
      | (C.And (r, a, g), s), (C.DProg (g_, dPool) as dp) ->
          let x = I.newEVar g_ (I.EClo (a, s)) in
          rSolve
            ( ps',
              (r, I.Dot (I.Exp x, s)),
              dp,
              function
              | s_ -> solve g s dp (function m -> sc (I.App (m, s_))) )
      | (C.Exists (I.Dec (_, a), r), s), (C.DProg (g, dPool) as dp)
        ->
          let x = I.newEVar g (I.EClo (a, s)) in
          rSolve
            ( ps',
              (r, I.Dot (I.Exp x, s)),
              dp,
              function s -> sc (I.App (x, s)) )
      | (C.Axists (I.ADec (_, d), r), s), (C.DProg (g, dPool) as dp)
        ->
          let x' = I.newAVar () in
          rSolve
            (ps', (r, I.Dot (I.Exp (I.EClo (x', I.Shift (-d))), s)), dp, sc)
      (* C.In is like C.And but for meta-level ("virtual") dependencies *)
      | (C.In (r, a, g), s), (C.DProg (g_, dPool) as dp) ->
          let x = I.newEVar g_ (I.EClo (a, s)) in
          rSolve
            ( ps',
              (r, I.Dot (I.Exp x, s)),
              dp,
              function
              | s_ -> solve g s dp (function m -> sc (I.App (m, s_))) )

    and aSolve (a, b, cnstr, sc) = match a, b with
      | (C.Trivial, s), dp ->
          begin if Assign.solveCnstr cnstr then sc () else ()
          end
      | (C.UnifyEq (g', e1, n, eqns), s), (C.DProg (g, dPool) as dp) ->
          let g'' = compose (g, g') in
          let s' = shiftSub (g', s) in
          begin if Assign.unifiable g'' (n, s') (e1, s') then
            aSolve ((eqns, s), dp, cnstr, sc)
          else ()
          end

    and matchAtom
        (((I.Root (ha, s_), s) as ps'), (C.DProg (g, dPool) as dp), sc) =
      let deterministic = C.detTableCheck (cidFromHead ha) in
      let exception SucceedOnce of I.spine in
      let rec matchSig = function
        | [] -> ()
        | hc :: sgn' ->
            let (C.SClause r) = C.sProgLookup (cidFromHead hc) in
            CsManager.trail (function () ->
                rSolve
                  (ps', (r, I.id), dp, function s -> sc (I.Root (hc, s))));
            matchSig sgn'
      in
      let rec matchSigDet = function
        | [] -> ()
        | hc :: sgn' -> (
            let (C.SClause r) = C.sProgLookup (cidFromHead hc) in
            try
              begin
                CsManager.trail (function () ->
                    rSolve
                      ( ps',
                        (r, I.id),
                        dp,
                        function s -> raise (SucceedOnce s) ));
                matchSigDet sgn'
              end
            with SucceedOnce s -> sc (I.Root (hc, s)))
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
                    CsManager.trail (function () ->
                        rSolve
                          ( ps',
                            (r, I.comp s (I.Shift k)),
                            dp,
                            function s -> raise (SucceedOnce s) ));
                    matchDProg (dPool', k + 1)
                  end
                with SucceedOnce s -> sc (I.Root (I.BVar k, s))
              else begin
                CsManager.trail (function () ->
                    rSolve
                      ( ps',
                        (r, I.comp s (I.Shift k)),
                        dp,
                        function s -> sc (I.Root (I.BVar k, s)) ));
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
  (* solve ((g, s), dp, sc) = ()
     Invariants:
       dp = (G, dPool) where  G ~ dPool  (context G matches dPool)
       G |- s : G'
       G' |- g  goal
       if  G |- M : g[s]
       then  sc M  is evaluated

     Effects: instantiation of EVars in g, s, and dp
              any effect  sc M  might have
  *)
  (*      val D' = I.decSub (D, s) *)
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
  *)
  (* effect: instantiate EVars *)
  (* call success continuation *)
  (* fail *)
  (* is this EVar redundant? -fp *)
  (* same effect as s^-1 *)
  (* we don't increase the proof term here! *)
  (* aSolve ((ag, s), dp, sc) = ()
     Invariants:
       dp = (G, dPool) where G ~ dPool
       G |- s : G'
       if G |- ag[s] auxgoal
       then sc () is evaluated
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
  (* matchSig [c1,...,cn] = ()
           try each constant ci in turn for solving atomic goal ps', starting
           with c1.

           #succeeds >= 1 (succeeds at least once)
        *)
  (* return unit on failure *)
  (* trail to undo EVar instantiations *)
  (* matchSigDet [c1,...,cn] = ()
           try each constant ci in turn for solving atomic goal ps', starting
           with c1.

           succeeds exactly once (#succeeds = 1)
        *)
  (* return unit on failure *)
  (* trail to undo EVar instantiations *)
  (* matchDProg (dPool, k) = ()
           where k is the index of dPool in global dPool from call to matchAtom.
           Try each local assumption for solving atomic goal ps', starting
           with the most recent one.
        *)
  (* dynamic program exhausted, try signature *)
  (* #succeeds = 1 *)
  (* trail to undo EVar instantiations *)
  (* #succeeds >= 1 -- allows backtracking *)
  (* trail to undo EVar instantiations *)
  let solve = solve
end
(*! sharing Names.IntSyn = IntSyn' !*)
(*! structure CsManager : CS_MANAGER !*)
(*! sharing CsManager.IntSyn = IntSyn' !*)
(* local ... *)
(* functor AbsMachine *)

(* # 1 "src/opsem/Absmachine.sml.ml" *)
