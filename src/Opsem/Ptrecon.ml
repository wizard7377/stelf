open! Intsyn.Lambda_
open! Names.Names_
open! Print.Print_
open! Index.Index_
open! Compile
open! CompSyn
open! Assign

(* # 1 "src/opsem/Ptrecon.sig.ml" *)

(* Abstract Machine guided by proof skeleton *)
(* Author: Brigitte Pientks *)
(* Modified: Jeff Polakow *)
(* Modified: Frank Pfenning *)
(* Proof term reconstruction by proof skeleton *)
include PTRECON
(* signature PTRECON *)

(* # 1 "src/opsem/Ptrecon.fun.ml" *)
open! Basis
open MemoTable

(* Abstract Machine execution guided by proof skeleton *)
(* Author: Brigitte Pientka *)
(* Modified: Jeff Polakow, Frank Pfenning, Larry Greenfield, Roberto Virga, Brigitte Pientka *)
(* Proof term reconstruction from proof skeleton *)
exception Error of string

let () =
  Printexc.register_printer (function Error msg -> Some msg | _ -> None)

module PtRecon (PtRecon__0 : sig
  (*! structure IntSyn' : INTSYN !*)
  (*! structure CompSyn' : COMPSYN !*)
  (*! sharing CompSyn'.IntSyn = IntSyn' !*)
  module Unify : UNIFY

  (*! sharing Unify.IntSyn = IntSyn' !*)
  module Assign : ASSIGN

  (*! sharing Assign.IntSyn = IntSyn' !*)
  (*! structure TableParam : TABLEPARAM !*)
  module MemoTable : MEMOTABLE.MEMOTABLE

  (*! sharing MemoTable.TableParam = TableParam !*)
  module Index : INDEX

  (*! sharing Index.IntSyn = IntSyn' !*)
  (* CPrint currently unused *)
  module CPrint : Cprint.CPRINT

  (*! sharing CPrint.IntSyn = IntSyn' !*)
  (*! sharing CPrint.CompSyn = CompSyn' !*)
  module Names : NAMES
end) : PTRECON = struct
  open PtRecon__0
  open! TableParam

  (*! structure IntSyn = IntSyn' !*)
  (*! structure CompSyn = CompSyn' !*)
  (*! structure TableParam = TableParam !*)
  open! struct
    module I = IntSyn
    module C = CompSyn
    module MT = MemoTable
  end

  exception Error = Error

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
  *)
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
  *)
  let rec solve' (o, a, b, sc) = match a, b with
    | (C.Atom p, s), (C.DProg (g, dPool) as dp) ->
        matchAtom (o, (p, s), dp, sc)
    | (C.Impl (r, a, ha, g), s), C.DProg (g_, dPool) ->
        let d' = I.Dec (None, I.EClo (a, s)) in
        begin if !TableParam.strengthen then
          begin match MT.memberCtx g_ (I.EClo (a, s)) g_ with
          | Some d ->
              let x = I.newEVar g_ (I.EClo (a, s)) in
              solve'
                ( o,
                  (g, I.Dot (I.Exp x, s)),
                  C.DProg (g_, dPool),
                  function o, m -> sc (o, I.Lam (d', m)) )
              (* need to reuse label for this assumption .... *)
          | None ->
              solve'
                ( o,
                  (g, I.dot1 s),
                  C.DProg (I.Decl (g_, d'), I.Decl (dPool, C.Dec (r, s, ha))),
                  function o, m -> sc (o, I.Lam (d', m)) )
          end
        else
          solve'
            ( o,
              (g, I.dot1 s),
              C.DProg (I.Decl (g_, d'), I.Decl (dPool, C.Dec (r, s, ha))),
              function o, m -> sc (o, I.Lam (d', m)) )
        end
        (*      solve' (O, (g, I.dot1 s), C.DProg (I.Decl(G, D'), I.Decl (dPool, C.Dec (r, s, Ha))),
               (fn (O,M) => sc (O, (I.Lam (D', M)))))*)
    | (C.All (d, g), s), C.DProg (g_, dPool) ->
        let d' = Names.decLUName g_ (I.decSub d s) in
        solve'
          ( o,
            (g, I.dot1 s),
            C.DProg (I.Decl (g_, d'), I.Decl (dPool, C.Parameter)),
            function o, m -> sc (o, I.Lam (d', m)) )
  (* val D' = I.decSub (D, s) *)

  and rSolve (o, ps', a, b, sc) = match a, b with
    | (C.Eq q, s), C.DProg (g, dPool) ->
        begin if Unify.unifiable g (q, s) ps' then sc (o, I.Nil)
        else
          let () = ignore begin
              print "Unification Failed -- SHOULD NEVER HAPPEN!\n";
              begin
                print
                  (Print.expToString g (I.EClo (fst ps', snd ps')) ^ " unify ");
                print (Print.expToString g (I.EClo (q, s)) ^ "\n")
              end
            end in
          ()
        end
    | (C.Assign (q, eqns), s), (C.DProg (g, dPool) as dp) ->
        begin match Assign.assignable g ps' (q, s) with
        | Some cnstr ->
            begin if aSolve ((eqns, s), dp, cnstr) then sc (o, I.Nil)
            else print "aSolve cnstr not solvable -- SHOULD NEVER HAPPEN\n"
            end
        | None -> print "Clause Head not assignable -- SHOULD NEVER HAPPEN\n"
        end
    | (C.And (r, a, g), s), (C.DProg (g_, dPool) as dp) ->
        let x = I.newEVar g_ (I.EClo (a, s)) in
        rSolve
          ( o,
            ps',
            (r, I.Dot (I.Exp x, s)),
            dp,
            function
            | o, s_ ->
                solve'
                  (o, (g, s), dp, function o, m -> sc (o, I.App (m, s_)))
          )
        (* is this EVar redundant? -fp *)
    | (C.Exists (I.Dec (_, a), r), s), (C.DProg (g, dPool) as dp)
      ->
        let x = I.newEVar g (I.EClo (a, s)) in
        rSolve
          ( o,
            ps',
            (r, I.Dot (I.Exp x, s)),
            dp,
            function o, s -> sc (o, I.App (x, s)) )
    | (C.Axists (I.ADec (Some x, d), r), s), (C.DProg (g, dPool) as dp) ->
        let x' = I.newAVar () in
        rSolve
          (o, ps', (r, I.Dot (I.Exp (I.EClo (x', I.Shift (-d))), s)), dp, sc)
  (* we don't increase the proof term here! *)
  (* fail *)

  and aSolve (a, b, cnstr) = match a, b with
    | (trivial, s), dp -> Assign.solveCnstr cnstr
    | (C.UnifyEq (g', e1, n, eqns), s), (C.DProg (g, dPool) as dp) ->
        let g'' = compose' (g', g) in
        let s' = shift (g', s) in
        Assign.unifiable g'' (n, s') (e1, s')
        && aSolve ((eqns, s), dp, cnstr)

  and matchAtom
      (ho :: o, ((I.Root (ha, s_), s) as ps'), (C.DProg (g, dPool) as dp), sc)
      =
    let rec matchSig (a, k) = match a with
      | [] -> raise (Error " \noracle #Pc does not exist \n")
      | (I.Const c as hc) :: sgn' ->
          begin if c = k then
            let (C.SClause r) = C.sProgLookup (cidFromHead hc) in
            rSolve
              ( o,
                ps',
                (r, I.id),
                dp,
                function o, s -> sc (o, I.Root (hc, s)) )
          else matchSig (sgn', k)
          end
      | (I.Def d as hc) :: sgn' ->
          begin if d = k then
            let (C.SClause r) = C.sProgLookup (cidFromHead hc) in
            rSolve
              ( o,
                ps',
                (r, I.id),
                dp,
                function o, s -> sc (o, I.Root (hc, s)) )
          else matchSig (sgn', k)
          end
      (* should not happen *)
    in
    let rec matchDProg (a, i, k) = match a, i with
      | I.Null, i ->
          raise
            (Error
               "\n\
               \ selected dynamic clause number does not exist in current \
                dynamic clause pool!\n")
      | I.Decl (dPool', C.Dec (r, s, ha')), 1 ->
          begin if eqHead (ha, ha') then
            rSolve
              ( o,
                ps',
                (r, I.comp s (I.Shift k)),
                dp,
                function o, s -> sc (o, I.Root (I.BVar k, s)) )
          else
            raise
              (Error "\n selected dynamic clause does not match current goal!\n")
          end
      | I.Decl (dPool', dc), i -> matchDProg (dPool', i - 1, k)
    in
    begin match ho with
    | C.Pc i -> matchSig (Index.lookup (cidFromHead ha), i)
    | C.Dc i -> matchDProg (dPool, i, i)
    | C.Csolver u -> sc (o, u)
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
  *)
  (* aSolve ((ag, s), dp, sc) = res
     Invariants:
       dp = (G, dPool) where G ~ dPool
       G |- s : G'
       if G |- ag[s] auxgoal
       then sc () is evaluated with return value res
       else res = Fail
     Effects: instantiation of EVars in ag[s], dp and sc () *)
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
  *)
  let solve (o, (g, s), (C.DProg (g_, dPool) as dp), sc) =
    try solve' (o, (g, s), dp, sc) with Error msg -> print msg
end
(*! sharing Names.IntSyn = IntSyn' !*)
(*! structure CsManager : CS_MANAGER !*)
(*! sharing CsManager.IntSyn = IntSyn' !*)
(* local ... *)
(* functor PtRecon *)
(* # 1 "src/opsem/Ptrecon.sml.ml" *)
