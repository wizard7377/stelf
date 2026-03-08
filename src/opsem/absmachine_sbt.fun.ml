open! Index
open! Basis

(* Abstract Machine using substitution trees *)
(* Author: Iliano Cervesato *)
(* Modified: Jeff Polakow, Frank Pfenning, Larry Greenfield, Roberto Virga *)
module AbsMachineSbt (AbsMachineSbt__0 : sig
  (*! structure IntSyn' : INTSYN !*)
  (*! structure CompSyn' : COMPSYN !*)
  (*! sharing CompSyn'.IntSyn = IntSyn' !*)
  module Unify : UNIFY

  (*! sharing Unify.IntSyn = IntSyn' !*)
  module SubTree : SUBTREE

  (*! sharing SubTree.IntSyn = IntSyn' !*)
  (*! sharing SubTree.CompSyn = CompSyn' !*)
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
end) : ABSMACHINESBT = struct
  (*! structure IntSyn = IntSyn' !*)
  (*! structure CompSyn = CompSyn' !*)
  open! struct
    module I = IntSyn
    module C = CompSyn

    let mSig :
        ((IntSyn.exp_ * IntSyn.sub_)
         * CompSyn.dProg_
         * (CompSyn.flatterm_ list -> unit) ->
        unit)
        ref =
      ref (function ps, dp, sc -> ())

    let rec cidFromHead = function I.Const a -> a | I.Def a -> a

    let rec eqHead = function
      | I.Const a, I.Const a' -> a = a'
      | I.Def a, I.Def a' -> a = a'
      | _ -> false

    let rec compose' = function
      | null_, g_ -> g_
      | IntSyn.Decl (g_, d_), g'_ -> IntSyn.Decl (compose' (g_, g'_), d_)

    let rec shift = function
      | null_, s -> s
      | IntSyn.Decl (g_, d_), s -> I.dot1 (shift (g_, s))

    let rec invShiftN (n, s) =
      begin if n = 0 then I.comp (I.invShift, s)
      else I.comp (I.invShift, invShiftN (n - 1, s))
      end

    let rec raiseType = function
      | null_, v_ -> v_
      | I.Decl (g_, d_), v_ -> raiseType (g_, I.Pi ((d_, I.maybe_), v_))

    let rec printSub = function
      | IntSyn.Shift n -> print (("Shift " ^ Int.toString n) ^ "\n")
      | IntSyn.Dot (IntSyn.Idx n, s) -> begin
          print (("Idx " ^ Int.toString n) ^ " . ");
          printSub s
        end
      | IntSyn.Dot (IntSyn.Exp (IntSyn.EVar (_, _, _, _)), s) -> begin
          print "Exp (EVar _ ). ";
          printSub s
        end
      | IntSyn.Dot (IntSyn.Exp (IntSyn.AVar _), s) -> begin
          print "Exp (AVar _ ). ";
          printSub s
        end
      | IntSyn.Dot (IntSyn.Exp (IntSyn.EClo (IntSyn.AVar _, _)), s) -> begin
          print "Exp (AVar _ ). ";
          printSub s
        end
      | IntSyn.Dot (IntSyn.Exp (IntSyn.EClo (_, _)), s) -> begin
          print "Exp (EClo _ ). ";
          printSub s
        end
      | IntSyn.Dot (IntSyn.Exp _, s) -> begin
          print "Exp (_ ). ";
          printSub s
        end
      | IntSyn.Dot (undef_, s) -> begin
          print "Undef . ";
          printSub s
        end

    let rec ctxToEVarSub = function
      | gglobal_, null_, s -> s
      | gglobal_, I.Decl (g_, I.Dec (_, a_)), s ->
          let s' = ctxToEVarSub (gglobal_, g_, s) in
          let x_ = I.newEVar (gglobal_, I.EClo (a_, s')) in
          I.Dot (I.Exp x_, s')
      | gglobal_, I.Decl (g_, I.ADec (_, d)), s ->
          let x_ = I.newAVar () in
          I.Dot
            (I.Exp (I.EClo (x_, I.Shift (-d))), ctxToEVarSub (gglobal_, g_, s))

    let rec solve' = function
      | (C.Atom p, s), (C.DProg (g_, dpool) as dp), sc ->
          matchAtom ((p, s), dp, sc)
      | (C.Impl (r, a_, ha_, g), s), C.DProg (g_, dPool), sc ->
          let d'_ = I.Dec (None, I.EClo (a_, s)) in
          solve'
            ( (g, I.dot1 s),
              C.DProg (I.Decl (g_, d'_), I.Decl (dPool, C.Dec (r, s, ha_))),
              sc )
      | (C.All (d_, g), s), C.DProg (g_, dPool), sc ->
          let d'_ = Names.decLUName (g_, I.decSub (d_, s)) in
          solve'
            ( (g, I.dot1 s),
              C.DProg (I.Decl (g_, d'_), I.Decl (dPool, C.parameter_)),
              sc )

    and rSolve = function
      | ps', (C.Eq q_, s), C.DProg (g_, dPool), sc -> begin
          if Unify.unifiable (g_, ps', (q_, s)) then sc [] else ()
        end
      | ps', (C.Assign (q_, eqns), s), (C.DProg (g_, dPool) as dp), sc -> begin
          match Assign.assignable (g_, ps', (q_, s)) with
          | Some cnstr -> aSolve ((eqns, s), dp, cnstr, function () -> sc [])
          | None -> ()
        end
      | ps', (C.And (r, a_, g), s), (C.DProg (g_, dPool) as dp), sc ->
          let x_ = I.newEVar (g_, I.EClo (a_, s)) in
          rSolve
            ( ps',
              (r, I.Dot (I.Exp x_, s)),
              dp,
              function
              | skel1 ->
                  solve' ((g, s), dp, function skel2 -> sc (skel1 @ skel2)) )
      | ps', (C.Exists (I.Dec (_, a_), r), s), (C.DProg (g_, dPool) as dp), sc
        ->
          let x_ = I.newEVar (g_, I.EClo (a_, s)) in
          rSolve (ps', (r, I.Dot (I.Exp x_, s)), dp, sc)
      | ps', (C.Axists (I.ADec (_, d), r), s), (C.DProg (g_, dPool) as dp), sc
        ->
          let x'_ = I.newAVar () in
          rSolve
            (ps', (r, I.Dot (I.Exp (I.EClo (x'_, I.Shift (-d))), s)), dp, sc)

    and aSolve = function
      | (trivial_, s), dp, cnstr, sc -> begin
          if Assign.solveCnstr cnstr then sc () else ()
        end
      | ( (C.UnifyEq (g'_, e1, n_, eqns), s),
          (C.DProg (g_, dPool) as dp),
          cnstr,
          sc ) ->
          let g''_ = compose' (g'_, g_) in
          let s' = shift (g'_, s) in
          begin if Assign.unifiable (g''_, (n_, s'), (e1, s')) then
            aSolve ((eqns, s), dp, cnstr, sc)
          else ()
          end

    and sSolve = function
      | (true_, s), dp, sc -> sc []
      | (C.Conjunct (g, a_, sgoals_), s), (C.DProg (g_, dPool) as dp), sc ->
          solve'
            ( (g, s),
              dp,
              function
              | skel1 ->
                  sSolve
                    ((sgoals_, s), dp, function skel2 -> sc (skel1 @ skel2)) )

    and matchSig
        (((I.Root (ha_, s_), s) as ps'), (C.DProg (g_, dPool) as dp), sc) =
      let rec mSig = function
        | [] -> ()
        | (I.Const c as hc_) :: sgn' ->
            let (C.SClause r) = C.sProgLookup (cidFromHead hc_) in
            begin
              Cs_manager.trail (function () ->
                  rSolve (ps', (r, I.id), dp, function s_ -> sc (C.Pc c :: s_)));
              mSig sgn'
            end
      in
      mSig (Index.lookup (cidFromHead ha_))

    and matchIndexSig
        (((I.Root (ha_, s_), s) as ps'), (C.DProg (g_, dPool) as dp), sc) =
      SubTree.matchSig
        ( cidFromHead ha_,
          g_,
          ps',
          function
          | (conjGoals_, s), clauseName ->
              sSolve
                ( (conjGoals_, s),
                  dp,
                  function s_ -> sc (C.Pc clauseName :: s_) ) )

    and matchAtom
        (((I.Root (ha_, s_), s) as ps'), (C.DProg (g_, dPool) as dp), sc) =
      let rec matchDProg = function
        | null_, _ -> ( ! ) mSig (ps', dp, sc)
        | I.Decl (dPool', C.Dec (r, s, ha'_)), k -> begin
            if eqHead (ha_, ha'_) then begin
              Cs_manager.trail (function () ->
                  rSolve
                    ( ps',
                      (r, I.comp (s, I.Shift k)),
                      dp,
                      function s_ -> sc (C.Dc k :: s_) ));
              matchDProg (dPool', k + 1)
            end
            else matchDProg (dPool', k + 1)
          end
        | I.Decl (dPool', parameter_), k -> matchDProg (dPool', k + 1)
      in
      let rec matchConstraint (Solve_, try_) =
        let succeeded =
          Cs_manager.trail (function () ->
              begin match Solve_ (g_, I.SClo (s_, s), try_) with
              | Some u_ -> begin
                  sc [ C.Csolver u_ ];
                  true
                end
              | None -> false
              end)
        in
        begin if succeeded then matchConstraint (Solve_, try_ + 1) else ()
        end
      in
      begin match I.constStatus (cidFromHead ha_) with
      | I.Constraint (cs, Solve_) -> matchConstraint (Solve_, 0)
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
  (* ctxToEVarSub D = s*)
  (* solve' ((g, s), dp, sc) = res
     Invariants:
       dp = (G, dPool) where  G ~ dPool  (context G matches dPool)
       G |- s : G'
       G' |- g  goal
       if  G |- M : g[s]
       then  sc M  is evaluated with return value res
       else Fail
     Effects: instantiation of EVars in g, s, and dp
              any effect  sc M  might have
  *)
  (* rSolve ((p,s'), (r,s), dp, sc) = res
     Invariants:
       dp = (G, dPool) where G ~ dPool
       G |- s : G'
       G' |- r  resgoal
       G |- s' : G''
       G'' |- p : H @ S' (mod whnf)
       if G |- S : r[s]
       then sc S is evaluated with return value res
       else Fail
     Effects: instantiation of EVars in p[s'], r[s], and dp
              any effect  sc S  might have
  *)
  (* effect: instantiate EVars *)
  (* call success continuation *)
  (* fail *)
  (* is this EVar redundant? -fp *)
  (* we don't increase the proof term here! *)
  (* aSolve ((ag, s), dp, sc) = res
     Invariants:
       dp = (G, dPool) where G ~ dPool
       G |- s : G'
       if G |- ag[s] auxgoal
       then sc () is evaluated with return value res
       else Fail
     Effects: instantiation of EVars in ag[s], dp and sc () *)
  (* Fail *)
  (* Fail *)
  (* solve subgoals of static program clauses *)
  (* sSolve ((sg, s) , dp , sc =
 if  dp = (G, dPool) where G ~ dPool
     G |- s : G'
     sg = g1 and g2 ...and gk
     for every subgoal gi, G' |- gi
                           G  | gi[s]
   then
      sc () is evaluated
   else Fail

   Effects: instantiation of EVars in gi[s], dp, sc
*)
  (* match signature *)
  (* return on failure *)
  (* trail to undo EVar instantiations *)
  (* matchatom ((p, s), dp, sc) => res
     Invariants:
       dp = (G, dPool) where G ~ dPool
       G |- s : G'
       G' |- p : type, p = H @ S mod whnf
       if G |- M :: p[s]
       then sc M is evaluated with return value res
       else Fail
     Effects: instantiation of EVars in p[s] and dp
              any effect  sc M  might have

     This first tries the local assumptions in dp then
     the static signature.
  *)
  (* matchDProg (dPool, k) = ()
           where k is the index of dPool in global dPool from call to matchAtom.
           Try each local assumption for solving atomic goal ps', starting
           with the most recent one.
        *)
  (* dynamic program exhausted, try signature
               there is a choice depending on how we compiled signature
             *)
  (* trail to undo EVar instantiations *)
  let rec solve args =
    begin match !CompSyn.optimize with
    | no_ -> begin
        mSig := matchSig;
        solve' args
      end
    | linearHeads_ -> begin
        mSig := matchSig;
        solve' args
      end
    | indexing_ -> begin
        mSig := matchIndexSig;
        solve' args
      end
    end
end
(*! sharing Names.IntSyn = IntSyn' !*)
(*! structure Cs_manager : CS_MANAGER !*)
(*! sharing Cs_manager.IntSyn = IntSyn'!*)
(* local ... *)
(* functor AbsMachineSbt *)
