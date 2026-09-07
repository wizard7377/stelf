open! Intsyn.Lambda_
open! Names.Names_
open! Print.Print_
open! Index.Index_
open! Solvers.Solvers_
open! Compile
open! CompSyn
open! Assign

(* # 1 "src/opsem/AbsmachineSbt.sig.ml" *)

(* Abstract Machine *)
(* Author: Iliano Cervesato *)
(* Modified: Jeff Polakow *)
(* Modified: Frank Pfenning *)
include ABSMACHINESBT
(* signature ABSMACHINESBT *)

(* # 1 "src/opsem/AbsmachineSbt.fun.ml" *)
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
  module SubTree : Subtree.SUBTREE

  (*! sharing SubTree.IntSyn = IntSyn' !*)
  (*! sharing SubTree.CompSyn = CompSyn' !*)
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
end) : ABSMACHINESBT = struct
  open AbsMachineSbt__0

  (*! structure IntSyn = IntSyn' !*)
  (*! structure CompSyn = CompSyn' !*)
  open! struct
    module I = IntSyn
    module C = CompSyn

    let mSig :
        ((IntSyn.exp * IntSyn.sub)
         * CompSyn.dProg
         * (CompSyn.flatterm list -> unit) ->
        unit)
        ref =
      ref (function ps, dp, sc -> ())

    let cidFromHead = function I.Const a -> a | I.Def a -> a

    let eqHead = function
      | I.Const a, I.Const a' -> a = a'
      | I.Def a, I.Def a' -> a = a'
      | _ -> false

    let rec compose' = function
      | I.Null, g -> g
      | IntSyn.Decl (g, d), g' -> IntSyn.Decl (compose' (g, g'), d)

    let rec shift (a, s) = match a with
      | I.Null -> s
      | IntSyn.Decl (g, d) -> I.dot1 (shift (g, s))

    let rec invShiftN (n, s) =
      begin if n = 0 then I.comp I.invShift s
      else I.comp I.invShift (invShiftN (n - 1, s))
      end

    let rec raiseType a1 b1 = match a1, b1 with
      | I.Null, v -> v
      | I.Decl (g, d), v -> raiseType g (I.Pi ((d, I.Maybe), v))

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
      | IntSyn.Dot (IntSyn.Undef, s) -> begin
          print "Undef . ";
          printSub s
        end

    let rec ctxToEVarSub (gglobal, a, s) = match a with
      | I.Null -> s
      | I.Decl (g, I.Dec (_, a)) ->
          let s' = ctxToEVarSub (gglobal, g, s) in
          let x = I.newEVar gglobal (I.EClo (a, s')) in
          I.Dot (I.Exp x, s')
      | I.Decl (g, I.ADec (_, d)) ->
          let x = I.newAVar () in
          I.Dot
            (I.Exp (I.EClo (x, I.Shift (-d))), ctxToEVarSub (gglobal, g, s))

    let rec solve' (a, b, sc) = match a, b with
      | (C.Atom p, s), (C.DProg (g, dpool) as dp) ->
          matchAtom ((p, s), dp, sc)
      | (C.Impl (r, a, ha, g), s), C.DProg (g_, dPool) ->
          let d' = I.Dec (None, I.EClo (a, s)) in
          solve'
            ( (g, I.dot1 s),
              C.DProg (I.Decl (g_, d'), I.Decl (dPool, C.Dec (r, s, ha))),
              sc )
      | (C.All (d, g), s), C.DProg (g_, dPool) ->
          let d' = Names.decLUName g_ (I.decSub d s) in
          solve'
            ( (g, I.dot1 s),
              C.DProg (I.Decl (g_, d'), I.Decl (dPool, C.Parameter)),
              sc )

    and rSolve (ps', a, b, sc) = match a, b with
      | (C.Eq q, s), C.DProg (g, dPool) ->
          begin if Unify.unifiable g ps' (q, s) then sc [] else ()
          end
      | (C.Assign (q, eqns), s), (C.DProg (g, dPool) as dp) ->
          begin match Assign.assignable g ps' (q, s) with
          | Some cnstr -> aSolve ((eqns, s), dp, cnstr, function () -> sc [])
          | None -> ()
          end
      | (C.And (r, a, g), s), (C.DProg (g_, dPool) as dp) ->
          let x = I.newEVar g_ (I.EClo (a, s)) in
          rSolve
            ( ps',
              (r, I.Dot (I.Exp x, s)),
              dp,
              function
              | skel1 ->
                  solve' ((g, s), dp, function skel2 -> sc (skel1 @ skel2)) )
      | (C.Exists (I.Dec (_, a), r), s), (C.DProg (g, dPool) as dp)
        ->
          let x = I.newEVar g (I.EClo (a, s)) in
          rSolve (ps', (r, I.Dot (I.Exp x, s)), dp, sc)
      | (C.Axists (I.ADec (_, d), r), s), (C.DProg (g, dPool) as dp)
        ->
          let x' = I.newAVar () in
          rSolve
            (ps', (r, I.Dot (I.Exp (I.EClo (x', I.Shift (-d))), s)), dp, sc)

    and aSolve (a, b, cnstr, sc) = match a, b with
      | (trivial, s), dp ->
          begin if Assign.solveCnstr cnstr then sc () else ()
          end
      | (C.UnifyEq (g', e1, n, eqns), s), (C.DProg (g, dPool) as dp) ->
          let g'' = compose' (g', g) in
          let s' = shift (g', s) in
          begin if Assign.unifiable g'' (n, s') (e1, s') then
            aSolve ((eqns, s), dp, cnstr, sc)
          else ()
          end

    and sSolve (a, b, sc) = match a, b with
      | (C.True, s), dp -> sc []
      | (C.Conjunct (g, a, sgoals), s), (C.DProg (g_, dPool) as dp) ->
          solve'
            ( (g, s),
              dp,
              function
              | skel1 ->
                  sSolve
                    ((sgoals, s), dp, function skel2 -> sc (skel1 @ skel2)) )

    and matchSig (((I.Root (ha, s_), s) as ps'), (C.DProg (g, dPool) as dp), sc)
        =
      let rec mSig = function
        | [] -> ()
        | (I.Const c as hc) :: sgn' ->
            let (C.SClause r) = C.sProgLookup (cidFromHead hc) in
            CsManager.trail (function () ->
                rSolve (ps', (r, I.id), dp, function s -> sc (C.Pc c :: s)));
            mSig sgn'
      in
      mSig (Index.lookup (cidFromHead ha))

    and matchIndexSig
        (((I.Root (ha, s_), s) as ps'), (C.DProg (g, dPool) as dp), sc) =
      SubTree.matchSig (cidFromHead ha) g ps' (function
        | (conjGoals, s), clauseName ->
            sSolve
              ((conjGoals, s), dp, function s -> sc (C.Pc clauseName :: s)))

    and matchAtom
        (((I.Root (ha, s_), s) as ps'), (C.DProg (g, dPool) as dp), sc) =
      let rec matchDProg (a, k) = match a with
        | I.Null -> ( ! ) mSig (ps', dp, sc)
        | I.Decl (dPool', C.Dec (r, s, ha')) ->
            begin if eqHead (ha, ha') then begin
              CsManager.trail (function () ->
                  rSolve
                    ( ps',
                      (r, I.comp s (I.Shift k)),
                      dp,
                      function s -> sc (C.Dc k :: s) ));
              matchDProg (dPool', k + 1)
            end
            else matchDProg (dPool', k + 1)
            end
        | I.Decl (dPool', parameter) -> matchDProg (dPool', k + 1)
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
  let solve a1 a2 b c =
    let args = ((a1, a2), b, c) in
    begin match !CompSyn.optimize with
    | CompSyn.No -> begin
        mSig := matchSig;
        solve' args
      end
    | CompSyn.LinearHeads -> begin
        mSig := matchSig;
        solve' args
      end
    | CompSyn.Indexing -> begin
        mSig := matchIndexSig;
        solve' args
      end
    end
end
(*! sharing Names.IntSyn = IntSyn' !*)
(*! structure CsManager : CS_MANAGER !*)
(*! sharing CsManager.IntSyn = IntSyn'!*)
(* local ... *)
(* functor AbsMachineSbt *)

(* # 1 "src/opsem/AbsmachineSbt.sml.ml" *)
