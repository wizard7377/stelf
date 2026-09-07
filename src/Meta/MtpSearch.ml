open! Global.Global_
open! Intsyn.Lambda_
open! Names.Names_
open! Print.Print_
open! Index.Index_
open! Compile
open! Compile.Compile_
open! Solvers.Solvers_

(* # 1 "src/meta/Search.sig.ml" *)
open Funsyn
open Statesyn
open MtpGlobal

(* Basic search engine: Version 1.3*)
(* Author: Carsten Schuermann *)
include MTPSEARCH
(* signature SEARCH *)

(* # 1 "src/meta/Search.fun.ml" *)
open! Basis

(* Search (based on abstract machine ) : Version 1.3 *)
(* Author: Carsten Schuermann *)
exception Error of string

let () =
  Printexc.register_printer (function Error msg -> Some msg | _ -> None)

module MTPSearch (MTPSearch__0 : sig
  module Global : GLOBAL

  (*! structure IntSyn' : INTSYN !*)
  module Abstract : ABSTRACT

  (*! sharing Abstract.IntSyn = IntSyn' !*)
  module MTPGlobal : MtpGlobal.MTPGLOBAL
  module StateSyn' : STATESYN.STATESYN

  (*! sharing StateSyn'.FunSyn.IntSyn = IntSyn' !*)
  (*! structure CompSyn' : COMPSYN !*)
  (*! sharing CompSyn'.IntSyn = IntSyn' !*)
  module Whnf : WHNF

  (*! sharing Whnf.IntSyn = IntSyn' !*)
  module Unify : UNIFY

  (*! sharing Unify.IntSyn = IntSyn'              !*)
  module Assign : Assign.ASSIGN

  (*! sharing Assign.IntSyn = IntSyn'   !*)
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
end) : MTPSEARCH.MTPSEARCH = struct
  (*! structure IntSyn = IntSyn' !*)
  open MTPSearch__0
  module StateSyn = StateSyn'

  (*! structure CompSyn = CompSyn' !*)
  exception Error = Error

  open! struct
    module I = IntSyn
    module C = CompSyn.CompSyn

    let rec isInstantiated = function
      | I.Root (I.Const cid, _) -> true
      | I.Pi (_, v) -> isInstantiated v
      | I.Root (I.Def cid, _) -> true
      | I.Redex (v, s) -> isInstantiated v
      | I.Lam (_, v) -> isInstantiated v
      | I.EVar ({ contents = Some v }, _, _, _) -> isInstantiated v
      | I.EClo (v, s) -> isInstantiated v
      | _ -> false

    let rec compose' = function
      | I.Null, g -> g
      | IntSyn.Decl (g, d), g' -> IntSyn.Decl (compose' (g, g'), d)

    let rec shift (a, s) = match a with
      | I.Null -> s
      | IntSyn.Decl (g, d) -> I.dot1 (shift (g, s))

    let rec raiseType a1 b1 = match a1, b1 with
      | I.Null, v -> v
      | I.Decl (g, d), v -> raiseType g (I.Pi ((d, I.Maybe), v))

    let exists p k =
      let rec exists' = function
        | I.Null -> false
        | I.Decl (k', y) -> p y || exists' k'
      in
      exists' k

    let rec occursInExp (r, vs) = occursInExpW (r, Whnf.whnf vs)

    and occursInExpW (r, a) = match a with
      | (I.Uni _, _) -> false
      | (I.Pi ((d, _), v), s) ->
          occursInDec (r, (d, s)) || occursInExp (r, (v, I.dot1 s))
      | (I.Root (_, s_), s) -> occursInSpine (r, (s_, s))
      | (I.Lam (d, v), s) ->
          occursInDec (r, (d, s)) || occursInExp (r, (v, I.dot1 s))
      | (I.EVar (r', _, v', _), s) -> r == r' || occursInExp (r, (v', s))
      | (I.FgnExp (csid, csfe), s) ->
          I.FgnExpStd.fold csid csfe
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

    let rec selectEVar = function
      | [] -> []
      | (I.EVar (r, _, _, { contents = [] }) as x) :: ge ->
          let xs = selectEVar ge in
          begin if nonIndex (r, xs) then xs @ [ x ] else xs
          end
      | (I.EVar (r, _, _, cnstrs) as x) :: ge ->
          let xs = selectEVar ge in
          begin if nonIndex (r, xs) then x :: xs else xs
          end

    let rec pruneCtx = function
      | g, 0 -> g
      | I.Decl (g, _), n -> pruneCtx (g, n - 1)

    let cidFromHead = function I.Const a -> a | I.Def a -> a | I.Skonst a -> a

    let eqHead = function
      | I.Const a, I.Const a' -> a = a'
      | I.Def a, I.Def a' -> a = a'
      | _ -> false

    let rec solve (max, depth, a, b, sc) = match a, b with
      | (C.Atom p, s), (C.DProg (g, dPool) as dp) ->
          matchAtom (max, depth, (p, s), dp, sc)
      | (C.Impl (r, a, ha, g), s), C.DProg (g_, dPool) ->
          let d' = I.Dec (None, I.EClo (a, s)) in
          solve
            ( max,
              depth + 1,
              (g, I.dot1 s),
              C.DProg (I.Decl (g_, d'), I.Decl (dPool, C.Dec (r, s, ha))),
              function m -> sc (I.Lam (d', m)) )
      | (C.All (d, g), s), C.DProg (g_, dPool) ->
          let d' = I.decSub d s in
          solve
            ( max,
              depth + 1,
              (g, I.dot1 s),
              C.DProg (I.Decl (g_, d'), I.Decl (dPool, C.Parameter)),
              function m -> sc (I.Lam (d', m)) )

    and rSolve (max, depth, ps', a, b, sc) = match a, b with
      | (C.Eq q, s), C.DProg (g, dPool) ->
          begin if Unify.unifiable g ps' (q, s) then sc I.Nil else ()
          end
      | (C.Assign (q, eqns), s), (C.DProg (g, dPool) as dp) ->
          begin match Assign.assignable g ps' (q, s) with
          | Some cnstr ->
              aSolve ((eqns, s), dp, cnstr, function () -> sc I.Nil)
          | None -> ()
          end
      | (C.And (r, a, g), s), (C.DProg (g_, dPool) as dp)
        ->
          let x = I.newEVar g_ (I.EClo (a, s)) in
          rSolve
            ( max,
              depth,
              ps',
              (r, I.Dot (I.Exp x, s)),
              dp,
              function
              | s_ ->
                  solve
                    ( max,
                      depth,
                      (g, s),
                      dp,
                      function m -> sc (I.App (m, s_)) ) )
      | (C.In (r, a, g), s), (C.DProg (g_, dPool) as dp)
        ->
          let g0 = pruneCtx (g_, depth) in
          let dPool0 = pruneCtx (dPool, depth) in
          let w = I.Shift depth in
          let iw = Whnf.invert w in
          let s' = I.comp s iw in
          let x = I.newEVar g0 (I.EClo (a, s')) in
          let x' = I.EClo (x, w) in
          rSolve
            ( max,
              depth,
              ps',
              (r, I.Dot (I.Exp x', s)),
              dp,
              function
              | s ->
                  begin if isInstantiated x then sc (I.App (x', s))
                  else
                    solve
                      ( max,
                        0,
                        (g, s'),
                        C.DProg (g0, dPool0),
                        function
                        | m -> (
                            try
                              begin
                                Unify.unify g0 (x, I.id) (m, I.id);
                                sc (I.App (I.EClo (m, w), s))
                              end
                            with Unify.Unify _ -> ()) )
                  end )
      | (C.Exists (I.Dec (_, a), r), s), (C.DProg (g, dPool) as dp) ->
          let x = I.newEVar g (I.EClo (a, s)) in
          rSolve
            ( max,
              depth,
              ps',
              (r, I.Dot (I.Exp x, s)),
              dp,
              function s -> sc (I.App (x, s)) )
      | (C.Axists (I.ADec (Some x, d), r), s), (C.DProg (g, dPool) as dp) ->
          let x' = I.newAVar () in
          rSolve
            ( max,
              depth,
              ps',
              (r, I.Dot (I.Exp (I.EClo (x', I.Shift (-d))), s)),
              dp,
              sc )

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

    and matchAtom (max, depth, a, b, sc) = match max, a, b with
      | 0, _, _ -> ()
      | max, ((I.Root (ha, _), _) as ps'), (C.DProg (g, dPool) as dp) ->
          let rec matchSig' = function
            | [] -> ()
            | hc :: sgn' ->
                let (C.SClause r) = C.sProgLookup (cidFromHead hc) in
                ignore (CsManager.trail (function () ->
                      rSolve
                        ( max - 1,
                          depth,
                          ps',
                          (r, I.id),
                          dp,
                          function s -> sc (I.Root (hc, s)) )));
                matchSig' sgn'
          in
          let rec matchDProg (a, n) = match a with
            | I.Null -> matchSig' (Index.lookup (cidFromHead ha))
            | I.Decl (dPool', C.Dec (r, s, ha')) ->
                begin if eqHead (ha, ha') then
                  let () = ignore (CsManager.trail (function () ->
                        rSolve
                          ( max - 1,
                            depth,
                            ps',
                            (r, I.comp s (I.Shift n)),
                            dp,
                            function s -> sc (I.Root (I.BVar n, s)) ))) in
                  matchDProg (dPool', n + 1)
                else matchDProg (dPool', n + 1)
                end
            | I.Decl (dPool', parameter) -> matchDProg (dPool', n + 1)
          in
          matchDProg (dPool, 1)

    and searchEx' arg__1 arg__2 =
      begin match (arg__1, arg__2) with
      | max, ([], sc) -> sc max
      | max, ((I.EVar (r, g, v, _) as x) :: ge, sc) ->
          solve
            ( max,
              0,
              (Compile.compileGoal g v, I.id),
              Compile.compileCtx false g,
              function
              | u' -> (
                  try
                    begin
                      Unify.unify g (x, I.id) (u', I.id);
                      searchEx' max (ge, sc)
                    end
                  with Unify.Unify _ -> ()) )
      end

    let deepen depth f p =
      let rec deepen' level =
        begin if level > depth then ()
        else begin
          begin if !Global.chatter > 5 then print "#" else ()
          end;
          begin
            f level p;
            deepen' (level + 1)
          end
        end
        end
      in
      deepen' 1

    let rec searchEx (it, depth) (ge, sc) =
      begin
        begin if !Global.chatter > 5 then print "[Search: " else ()
        end;
        begin
          deepen depth searchEx'
            ( selectEVar ge,
              function
              | max -> begin
                  begin if !Global.chatter > 5 then print "OK]\n" else ()
                  end;
                  let ge' =
                    foldr
                      (function
                        | (I.EVar (_, g, _, _) as x), l ->
                            Abstract.collectEVars g (x, I.id) l)
                      [] ge
                  in
                  let gE' = List.length ge' in
                  begin if gE' > 0 then
                    begin if it > 0 then searchEx (it - 1, 1) (ge', sc) else ()
                    end
                  else sc max
                  end
                end );
          begin
            begin if !Global.chatter > 5 then print "FAIL]\n" else ()
            end;
            ()
          end
        end
      end

    let search (maxFill, ge, sc) = searchEx (1, maxFill) (ge, sc)
  end

  (* isInstantiated (V) = SOME(cid) or NONE
       where cid is the type family of the atomic target type of V,
       NONE if V is a kind or object or have variable type.
    *)
  (* raiseType (G, V) = {{G}} V

       Invariant:
       If G |- V : L
       then  . |- {{G}} V : L

       All abstractions are potentially dependent.
    *)
  (* exists P K = B
       where B iff K = K1, Y, K2  s.t. P Y  holds
    *)
  (* occursInExp (r, (U, s)) = B,

       Invariant:
       If    G |- s : G1   G1 |- U : V
       then  B holds iff r occurs in (the normal form of) U
    *)
  (* hack - should consult cs  -rv *)
  (* nonIndex (r, GE) = B

       Invariant:
       B hold iff
        r does not occur in any type of EVars in GE
    *)
  (* select (GE, (V, s), acc) = acc'

       Invariant:
    *)
  (* Efficiency: repeated whnf for every subterm in Vs!!! *)
  (* Constraint case *)
  (* pruneCtx (G, n) = G'

       Invariant:
       If   |- G ctx
       and  G = G0, G1
       and  |G1| = n
       then |- G' = G0 ctx
    *)
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
  (* rsolve (max, depth, (p,s'), (r,s), (G,dPool), sc, (acc, k)) = ()
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
  (* is this EVar redundant? -fp *)
  (* G |- g goal *)
  (* G |- A : type *)
  (* G, A |- r resgoal *)
  (* G0, Gl  |- s : G *)
  (* G0, Gl  |- w : G0 *)
  (* G0 |- iw : G0, Gl *)
  (* G0 |- w : G *)
  (* G0 |- X : A[s'] *)
  (* G0, Gl |- X' : A[s'][w] = A[s] *)
  (* we don't increase the proof term here! *)
  (* aSolve ((ag, s), dp, sc) = res
     Invariants:
       dp = (G, dPool) where G ~ dPool
       G |- s : G'
       if G |- ag[s] auxgoal
       then sc () is evaluated with return value res
       else res = Fail
     Effects: instantiation of EVars in ag[s], dp and sc () *)
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
         checking the variable MTPGlobal.maxLevel
       then R' is the result of applying f to P and
         traversing all possible numbers up to MTPGlobal.maxLevel
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
  (* warning: iterative deepening depth is not propably updated.
                                             possible that it runs into an endless loop ? *)
  (* search (GE, sc) = ()

       Invariant:
       GE is a list of uninstantiated EVars
       and sc is a success continuation : int -> unit

       Side effect:
       success continuation will raise exception
    *)
  (* Shared contexts of EVars in GE may recompiled many times *)
  let searchEx a b c = search (a, b, c)
end
(*! sharing Names.IntSyn = IntSyn' !*)
(*! structure CsManager : CS_MANAGER !*)
(*! sharing CsManager.IntSyn = IntSyn' !*)
(* local ... *)
(* functor Search *)

(* # 1 "src/meta/MtpSearch.sml.ml" *)
