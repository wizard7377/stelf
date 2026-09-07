open! Global.Global_
open! Intsyn.Lambda_
open! Names.Names_
open! Print.Print_
open! Index.Index_
open! Compile
open! Compile.Compile_
open! Solvers.Solvers_

(* # 1 "src/m2/Search.sig.ml" *)
open Metasyn

(* Basic search engine *)
(* Author: Carsten Schuermann *)
include SEARCH
(* signature SEARCH *)

(* # 1 "src/m2/Search.fun.ml" *)
open! Basis
open Metasyn
open MetaGlobal

(* Search (based on abstract machine ) *)
(* Author: Carsten Schuermann *)

exception Error of string

let () =
  Printexc.register_printer (function Error msg -> Some msg | _ -> None)

module OLDSearch (OLDSearch__0 : sig
  (*! structure IntSyn' : INTSYN !*)
  module MetaGlobal : METAGLOBAL.METAGLOBAL
  module MetaSyn' : Metasyn.METASYN

  (*! sharing MetaSyn'.IntSyn = IntSyn' !*)
  (*! structure CompSyn' : COMPSYN !*)
  (*! sharing CompSyn'.IntSyn = IntSyn' !*)
  module Whnf : WHNF

  (*! sharing Whnf.IntSyn = IntSyn' !*)
  module Unify : UNIFY

  (*! sharing Unify.IntSyn = IntSyn' !*)
  module Assign : Assign.ASSIGN

  (*! sharing Assign.IntSyn = IntSyn' !*)
  module Index : INDEX

  (*! sharing Index.IntSyn = IntSyn' !*)
  module Compile : COMPILE

  (*! sharing Compile.IntSyn = IntSyn' !*)
  (*! sharing Compile.CompSyn = CompSyn' !*)
  module CPrint : Cprint.CPRINT

  (*! sharing CPrint.IntSyn = IntSyn' !*)
  (*! sharing CPrint.CompSyn = CompSyn' !*)
  module Print : PRINT

  (*! sharing Print.IntSyn = IntSyn' !*)
  module Names : NAMES
end) : OLDSEARCH with module MetaSyn = OLDSearch__0.MetaSyn' = struct
  open OLDSearch__0

  (*! structure IntSyn = IntSyn' !*)
  module MetaSyn = MetaSyn'

  (*! structure CompSyn = CompSyn' !*)
  exception Error = Error

  open! struct
    module I = IntSyn
    module M = MetaSyn
    module C = CompSyn.CompSyn

    let rec compose = function
      | I.Null, g' -> g'
      | I.Decl (g, d), g' -> I.Decl (compose (g, g'), d)

    let rec shiftSub (a, s) = match a with
      | I.Null -> I.id
      | I.Decl (g, d) -> I.dot1 (shiftSub (g, s))

    let cidFromHead = function I.Const a -> a | I.Def a -> a | I.Skonst a -> a

    let eqHead = function
      | I.Const a, I.Const a' -> a = a'
      | I.Def a, I.Def a' -> a = a'
      | _ -> false

    let rec solve (a, dp, sc, acck) = match a, dp with
      | (C.Atom p, s), dp -> matchAtom ((p, s), dp, sc, acck)
      | (C.Impl (r, a, h, g), s), C.DProg (g_, dPool) ->
          let d' = I.Dec (None, I.EClo (a, s)) in
          solve
            ( (g, I.dot1 s),
              C.DProg (I.Decl (g_, d'), I.Decl (dPool, C.Dec (r, s, h))),
              (function m, acck' -> sc (I.Lam (d', m), acck')),
              acck )
      | (C.All (d, g), s), C.DProg (g_, dPool) ->
          let d' = I.decSub d s in
          solve
            ( (g, I.dot1 s),
              C.DProg (I.Decl (g_, d'), I.Decl (dPool, C.Parameter)),
              (function m, acck' -> sc (I.Lam (d', m), acck')),
              acck )

    and rSolve (ps', a, b, sc, c) = match a, b, c with
      | (C.Eq q, s), C.DProg (g, dPool), ((acc, k) as acck) ->
          begin if Unify.unifiable g ps' (q, s) then sc (I.Nil, acck)
          else acc
          end
      | (C.Assign (q, eqns), s), (C.DProg (g, dPool) as dp), acck ->
          begin match Assign.assignable g ps' (q, s) with
          | Some cnstr ->
              aSolve ((eqns, s), dp, cnstr, function () -> sc (I.Nil, acck))
          | None -> acck |> fst
          end
      | (C.And (r, a, g), s), (C.DProg (g_, dPool) as dp), acck ->
          let x = I.newEVar g_ (I.EClo (a, s)) in
          rSolve
            ( ps',
              (r, I.Dot (I.Exp x, s)),
              dp,
              (function
              | s_, acck' ->
                  solve
                    ( (g, s),
                      dp,
                      (function
                      | m, acck'' -> (
                          try
                            begin
                              Unify.unify g_ (x, I.id) (m, I.id);
                              sc (I.App (m, s_), acck'')
                            end
                          with Unify.Unify _ -> fst acck')),
                      acck' )),
              acck )
      | (C.Exists (I.Dec (_, a), r), s), (C.DProg (g, dPool) as dp), acck ->
          let x = I.newEVar g (I.EClo (a, s)) in
          rSolve
            ( ps',
              (r, I.Dot (I.Exp x, s)),
              dp,
              (function s, acck' -> sc (I.App (x, s), acck')),
              acck )
      | (C.Axists (I.ADec (_, d), r), s), (C.DProg (g, dPool) as dp), acck ->
          let x' = I.newAVar () in
          rSolve
            ( ps',
              (r, I.Dot (I.Exp (I.EClo (x', I.Shift (-d))), s)),
              dp,
              sc,
              acck )

    and aSolve (a, b, cnstr, sc) = match a, b with
      | (C.Trivial, s), dp ->
          if Assign.solveCnstr cnstr then sc () else []
      | (C.UnifyEq (g', e1, n, eqns), s), (C.DProg (g, dPool) as dp) ->
          let g'' = compose (g', g) in
          let s' = shiftSub (g', s) in
          begin if Assign.unifiable g'' (n, s') (e1, s') then
            aSolve ((eqns, s), dp, cnstr, sc)
          else []
          end

    and matchAtom
        (((I.Root (ha, _), _) as ps'), (C.DProg (g, dPool) as dp), sc, (acc, k))
        =
      let matchSig acc' =
        let rec matchSig' (a, acc'') = match a with
          | [] -> acc''
          | hc :: sgn' ->
              let (C.SClause r) = C.sProgLookup (cidFromHead hc) in
              let acc''' =
                CsManager.trail (function () ->
                    rSolve
                      ( ps',
                        (r, I.id),
                        dp,
                        (function s, acck' -> sc (I.Root (hc, s), acck')),
                        (acc'', k - 1) ))
              in
              matchSig' (sgn', acc''')
        in
        matchSig' (Index.lookup (cidFromHead ha), acc')
      in
      let rec matchDProg (a, n, acc') = match a with
        | I.Null -> matchSig acc'
        | I.Decl (dPool', C.Dec (r, s, ha')) ->
            begin if eqHead (ha, ha') then
              let acc'' =
                CsManager.trail (function () ->
                    rSolve
                      ( ps',
                        (r, I.comp s (I.Shift n)),
                        dp,
                        (function
                        | s, acck' -> sc (I.Root (I.BVar n, s), acck')),
                        (acc', k - 1) ))
              in
              matchDProg (dPool', n + 1, acc'')
            else matchDProg (dPool', n + 1, acc')
            end
        | I.Decl (dPool', parameter) ->
            matchDProg (dPool', n + 1, acc')
      in
      begin if k < 0 then acc else matchDProg (dPool, 1, acc)
      end

    let rec occursInExp (r, vs) = occursInExpW (r, Whnf.whnf vs)

    and occursInExpW (r, a) = match a with
      | (I.Uni _, _) -> false
      | (I.Pi ((d, _), v), s) ->
          occursInDec (r, (d, s)) || occursInExp (r, (v, I.dot1 s))
      | (I.Root (_, s_), s) -> occursInSpine (r, (s_, s))
      | (I.Lam (d, v), s) ->
          occursInDec (r, (d, s)) || occursInExp (r, (v, I.dot1 s))
      | (I.EVar (r', _, v', _), s) -> r == r' || occursInExp (r, (v', s))
      | (I.FgnExp (csid, fge), s) ->
          I.FgnExpStd.fold csid fge
            (function u, b -> b || occursInExp (r, (u, s)))
            false

    and occursInSpine (r, a) = match a with
      | (I.Nil, _) -> false
      | (I.SClo (s_, s'), s) -> occursInSpine (r, (s_, I.comp s' s))
      | (I.App (u, s_), s) ->
          occursInExp (r, (u, s)) || occursInSpine (r, (s_, s))

    and occursInDec (r, (I.Dec (_, v), s)) = occursInExp (r, (v, s))

    let rec nonIndex (r, a) = match a with
      | [] -> true
      | I.EVar (_, _, v, _) :: ge ->
          (not (occursInExp (r, (v, I.id)))) && nonIndex (r, ge)

    let rec selectEVar (a, vs, acc) = match a with
      | [] -> acc
      | (I.EVar (r, _, _, _) as x) :: ge ->
          begin if occursInExp (r, vs) && nonIndex (r, acc) then
            selectEVar (ge, vs, x :: acc)
          else selectEVar (ge, vs, acc)
          end

    let rec searchEx' arg__1 arg__2 =
      begin match (arg__1, arg__2) with
      | max, ([], sc) -> [ sc () ]
      | max, (I.EVar (r, g, v, _) :: ge, sc) ->
          solve
            ( (Compile.compileGoal g v, I.id),
              Compile.compileCtx false g,
              (function
              | u', (acc', _) -> begin
                  Unify.instantiateEVar r u' [];
                  searchEx' max (ge, sc)
                end),
              ([], max) )
      end

    let deepen f p =
      let rec deepen' (level, acc) =
        begin if level > !MetaGlobal.maxFill then acc
        else begin
          begin if !Global.chatter > 5 then print "#" else ()
          end;
          deepen' (level + 1, f level p)
        end
        end
      in
      deepen' (1, [])

    let searchEx g ge vs sc =
      begin
        begin if !Global.chatter > 5 then print "[Search: " else ()
        end;
        let results =
          deepen searchEx'
            (selectEVar (ge, vs, []), function params -> sc params)
        in
        begin match results with
        | [] ->
            begin if !Global.chatter > 5 then print "FAIL]\n" else ()
            end;
            raise (Error "No object found")
        | _ :: _ ->
            begin if !Global.chatter > 5 then print "OK]\n" else ()
            end;
            results
        end
      end

    let rec searchAll' (a, acc, sc) = match a with
      | [] -> sc acc
      | I.EVar (r, g, v, _) :: ge ->
          solve
            ( (Compile.compileGoal g v, I.id),
              Compile.compileCtx false g,
              (function
              | u', (acc', _) -> begin
                  Unify.instantiateEVar r u' [];
                  searchAll' (ge, acc', sc)
                end),
              (acc, !MetaGlobal.maxFill) )

    let searchAll g ge vs sc =
      searchAll' (selectEVar (ge, vs, []), [], sc)
  end

  (* only used for type families of compiled clauses *)
  (* solve ((g,s), (G,dPool), sc, (acc, k)) => ()
     Invariants:
       G |- s : G'
       G' |- g :: goal
       G ~ dPool  (context G matches dPool)
       acc is the accumulator of results
       and k is the max search depth limit
           (used in the existential case for iterative deepening,
            used in the universal case for max search depth)
       if  G |- M :: g[s] then G |- sc :: g[s] => Answer, Answer closed
  *)
  (* rsolve ((p,s'), (r,s), (G,dPool), sc, (acc, k)) = ()
     Invariants:
       G |- s : G'
       G' |- r :: resgoal
       G |- s' : G''
       G'' |- p :: atom
       G ~ dPool
       acc is the accumulator of results
       and k is the max search depth limit
           (used in the existential case for iterative deepening,
            used in the universal case for max search depth)
       if G |- S :: r[s] then G |- sc : (r >> p[s']) => Answer
  *)
  (* replaced below by above.  -fp Mon Aug 17 10:41:09 1998
        ((Unify.unify (ps', (Q, s)); sc (I.Nil, acck)) handle Unify.Unify _ => acc) *)
  (*
    | rSolve (ps', (C.Assign (Q, ag), s), dp, sc, acck as (acc, k)) =
        ((Assign.assign (ps', (Q, s));
          aSolve ((ag, s), dp, (fn () => sc (I.Nil, acck)) , acc))
          handle Unify.Unify _ => acc
               | Assign.Assign _ => acc)
    *)
  (* why doesn't it always succeed?
                                                                --cs *)
  (*    | rSolve (ps', (C.Axists (I.Dec (_, A), r), s), dp as C.DProg (G, dPool), sc, acck) =
        let
          val X = I.newEVar (G, I.EClo (A, s))
        in
          rSolve (ps', (r, I.Dot (I.Exp (X), s)), dp,
                  (fn (S, acck') => sc (S, acck')), acck)
        end
*)
  (* aSolve ... *)
  (* Fri Jan 15 16:04:39 1999 -fp,cs
    | aSolve ((C.Unify(I.Eqn(e1, e2), ag), s), dp, sc, acc) =
      ((Unify.unify ((e1, s), (e2, s));
        aSolve ((ag, s), dp, sc, acc))
       handle Unify.Unify _ => acc)
     *)
  (* matchatom ((p, s), (G, dPool), sc, (acc, k)) => ()
     G |- s : G'
     G' |- p :: atom
     G ~ dPool
     acc is the accumulator of results
     and k is the max search depth limit
         (used in the existential case for iterative deepening,
          used in the universal case for max search depth)
     if G |- M :: p[s] then G |- sc :: p[s] => Answer
  *)
  (* occursInExp (r, (U, s)) = B,

       Invariant:
       If    G |- s : G1   G1 |- U : V
       then  B holds iff r occurs in (the normal form of) U
    *)
  (* nonIndex (r, GE) = B

       Invariant:
       B hold iff
        r does not occur in any type of EVars in GE
    *)
  (* select (GE, (V, s), acc) = acc'

       Invariant:
       If   GE is a list of Evars
       and  G |- s : G'   G' |- V : L
       then acc' is a list of EVars (G', X') s.t.
         (0) it extends acc'
         (1) (G', X') occurs in V[s]
         (2) (G', X') is not an index Variable to any (G, X) in acc'.
    *)
  (* Efficiency: repeated whnf for every subterm in Vs!!! *)
  (* searchEx' max (GE, sc) = acc'

       Invariant:
       If   GE is a list of EVars to be instantiated
       and  max is the maximal number of constructors
       then if an instantiation of EVars in GE is found Success is raised
            otherwise searchEx' terminates with []
    *)
  (* contexts of EVars are recompiled for each search depth *)
  (* Possible optimization:
           Check if there are still variables left over
        *)
  (* deepen (f, P) = R'

       Invariant:
       If   f function expecting parameters P
         checking the variable MetaGlobal.maxLevel
       then R' is the result of applying f to P and
         traversing all possible numbers up to MetaGlobal.maxLevel
    *)
  (* searchEx (G, GE, (V, s), sc) = acc'
       Invariant:
       If   G |- s : G'   G' |- V : level
       and  GE is a list of EVars contained in V[s]
         where G |- X : VX
       and  sc is a function to be executed after all non-index variables have
         been instantiated
       then acc' is a list containing the one result from executing the success continuation
         All EVar's got instantiated with the smallest possible terms.
    *)
  (* searchAll' (GE, acc, sc) = acc'

       Invariant:
       If   GE is a list of EVars to be instantiated
       and  acc is list of already collected results of the success continuation
       then acc' is an extension of acc', containing the results of sc
         after trying all combinations of instantiations of EVars in GE
    *)
  (* Shared contexts of EVars in GE may recompiled many times *)
  (* searchAll (G, GE, (V, s), sc) = acc'

       Invariant:
       If   G |- s : G'   G' |- V : level
       and  GE is a list of EVars contained in V[s]
         where G |- X : VX
       and  sc is a function to be executed after all non-index variables have
         been instantiated
       then acc' is a list of results from executing the success continuation
    *)
  let searchEx = searchEx
  let searchAll = searchAll
end
(*! sharing Names.IntSyn = IntSyn' !*)
(*! structure CsManager : CS_MANAGER !*)
(*! sharing CsManager.IntSyn = IntSyn' !*)
(* local ... *)
(* functor Search *)

(* # 1 "src/m2/Search.sml.ml" *)
