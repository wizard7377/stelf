open! Global.Global_
open! Intsyn.Lambda_
open! Names.Names_
open! Print.Print_
open! Index.Index_
open! Compile
open! Compile.Compile_
open! Solvers.Solvers_

(* # 1 "src/meta/Uniquesearch.sig.ml" *)
open MtpGlobal
open Funsyn
open Statesyn

(* Basic search engine: Version 1.3*)
(* Author: Carsten Schuermann *)
include UNIQUESEARCH
(* signature SEARCH *)

(* # 1 "src/meta/Uniquesearch.fun.ml" *)
open! Basis

(* Search (based on abstract machine ) : Version 1.3 *)
(* Author: Carsten Schuermann *)
exception Error of string

let () =
  Printexc.register_printer (function Error msg -> Some msg | _ -> None)

module UniqueSearch (UniqueSearch__0 : sig
  module Global : GLOBAL

  (*! structure IntSyn' : INTSYN !*)
  (*! structure FunSyn' : FUNSYN !*)
  (*! sharing FunSyn'.IntSyn = IntSyn' !*)
  module StateSyn' : STATESYN.STATESYN

  (*! sharing StateSyn'.IntSyn = IntSyn' !*)
  (*! sharing StateSyn'.FunSyn = FunSyn' !*)
  module Abstract : ABSTRACT

  (*! sharing Abstract.IntSyn = IntSyn' !*)
  module MTPGlobal : MtpGlobal.MTPGLOBAL

  (*! structure CompSyn' : COMPSYN !*)
  (*! sharing CompSyn'.IntSyn = IntSyn' !*)
  module Whnf : WHNF

  (*! sharing Whnf.IntSyn = IntSyn' !*)
  module Unify : UNIFY

  (*! sharing Unify.IntSyn = IntSyn' !*)
  module Assign : Assign.ASSIGN

  (*! sharing Assign.IntSyn = IntSyn'                         !*)
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
end) : UNIQUESEARCH.UNIQUESEARCH = struct
  (*! structure IntSyn = IntSyn' !*)
  (*! structure FunSyn = FunSyn' !*)
  open UniqueSearch__0
  module StateSyn = StateSyn'

  (*! structure CompSyn = CompSyn' !*)
  exception Error = Error

  type nonrec acctype = IntSyn.exp

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

    let rec solve (max, depth, a, dp, sc, acc) = match a, dp with
      | (C.Atom p, s), dp ->
          matchAtom (max, depth, (p, s), dp, sc, acc)
      | (C.Impl (r, a, h, g), s), C.DProg (g_, dPool) ->
          let d' = I.Dec (None, I.EClo (a, s)) in
          solve
            ( max,
              depth + 1,
              (g, I.dot1 s),
              C.DProg (I.Decl (g_, d'), I.Decl (dPool, C.Dec (r, s, h))),
              (fun (m, acc') -> sc (I.Lam (d', m), acc')),
              acc )
      | (C.All (d, g), s), C.DProg (g_, dPool) ->
          let d' = I.decSub d s in
          solve
            ( max,
              depth + 1,
              (g, I.dot1 s),
              C.DProg (I.Decl (g_, d'), I.Decl (dPool, C.Parameter)),
              (fun (m, acc') -> sc (I.Lam (d', m), acc')),
              acc )

    and rSolve (max, depth, ps', a, b, sc, acc) = match a, b with
      | (C.Eq q, s), C.DProg (g, dPool) ->
          begin if Unify.unifiable g ps' (q, s) then sc (I.Nil, acc)
          else acc
          end
      | (C.Assign (q, eqns), s), (C.DProg (g, dPool) as dp) ->
          begin match Assign.assignable g ps' (q, s) with
          | Some cnstr ->
              aSolve ((eqns, s), dp, cnstr, (fun () -> sc (I.Nil, acc)), acc)
          | None -> acc
          end
      | (C.And (r, a, g), s), (C.DProg (g_, dPool) as dp) ->
          let x = I.newEVar g_ (I.EClo (a, s)) in
          rSolve
            ( max,
              depth,
              ps',
              (r, I.Dot (I.Exp x, s)),
              dp,
              (fun (s_, acc') ->
                solve
                  ( max,
                    depth,
                    (g, s),
                    dp,
                    (fun (m, acc'') -> sc (I.App (m, s_), acc'')),
                    acc' )),
              acc )
      | (C.In (r, a, g), s), (C.DProg (g_, dPool) as dp) ->
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
              (fun (s, acc') ->
                if isInstantiated x then sc (I.App (x', s), acc')
                else
                  solve
                    ( max,
                      0,
                      (g, s'),
                      C.DProg (g0, dPool0),
                      (fun (m, acc'') ->
                        try
                          Unify.unify g0 (x, I.id) (m, I.id);
                          sc (I.App (I.EClo (m, w), s), acc'')
                        with Unify.Unify _ -> acc''),
                      acc' )),
              acc )
      | (C.Exists (I.Dec (_, a), r), s), (C.DProg (g, dPool) as dp) ->
          let x = I.newEVar g (I.EClo (a, s)) in
          rSolve
            ( max,
              depth,
              ps',
              (r, I.Dot (I.Exp x, s)),
              dp,
              (fun (s, acc') -> sc (I.App (x, s), acc')),
              acc )
      | (C.Axists (I.ADec (Some x, d), r), s), (C.DProg (g, dPool) as dp) ->
          let x' = I.newAVar () in
          rSolve
            ( max,
              depth,
              ps',
              (r, I.Dot (I.Exp (I.EClo (x', I.Shift (-d))), s)),
              dp,
              sc,
              acc )

    and aSolve (a, b, cnstr, sc, acc) = match a, b with
      | (trivial, s), dp ->
          begin if Assign.solveCnstr cnstr then sc () else acc
          end
      | (C.UnifyEq (g', e1, n, eqns), s), (C.DProg (g, dPool) as dp) ->
          let g'' = compose' (g', g) in
          let s' = shift (g', s) in
          begin if Assign.unifiable g'' (n, s') (e1, s') then
            aSolve ((eqns, s), dp, cnstr, sc, acc)
          else acc
          end

    and matchAtom (max, depth, b, c, sc, acc) = match max, b, c with
      | 0, _, _ -> acc
      | max, ((I.Root (ha, _), _) as ps'), (C.DProg (g, dPool) as dp) ->
          let rec matchSig' (a, acc') = match a with
            | [] -> acc'
            | hc :: sgn' ->
                let (C.SClause r) = C.sProgLookup (cidFromHead hc) in
                let acc''' =
                  CsManager.trail (function () ->
                      rSolve
                        ( max - 1,
                          depth,
                          ps',
                          (r, I.id),
                          dp,
                          (fun (s, acc'') -> sc (I.Root (hc, s), acc'')),
                          acc' ))
                in
                matchSig' (sgn', acc''')
          in
          let rec matchDProg (a, n, acc') = match a with
            | I.Null -> matchSig' (Index.lookup (cidFromHead ha), acc')
            | I.Decl (dPool', C.Dec (r, s, ha')) ->
                begin if eqHead (ha, ha') then
                  let acc''' =
                    CsManager.trail (function () ->
                        rSolve
                          ( max - 1,
                            depth,
                            ps',
                            (r, I.comp s (I.Shift n)),
                            dp,
                            (fun (s, acc'') ->
                              sc (I.Root (I.BVar n, s), acc'')),
                            acc' ))
                  in
                  matchDProg (dPool', n + 1, acc''')
                else matchDProg (dPool', n + 1, acc')
                end
            | I.Decl (dPool', parameter) ->
                matchDProg (dPool', n + 1, acc')
          in
          matchDProg (dPool, 1, acc)

    and searchEx' arg__1 arg__2 =
      begin match (arg__1, arg__2) with
      | max, ([], sc, acc) -> sc acc
      | max, ((I.EVar (r, g, v, _) as x) :: ge, sc, acc) ->
          solve
            ( max,
              0,
              (Compile.compileGoal g v, I.id),
              Compile.compileCtx false g,
              (fun (u', acc') ->
                try
                  Unify.unify g (x, I.id) (u', I.id);
                  searchEx' max (ge, sc, acc')
                with Unify.Unify _ -> acc'),
              acc )
      end

    let rec searchEx (it, depth) (ge, sc, acc) =
      begin
        begin if !Global.chatter > 5 then print "[Search: " else ()
        end;
        searchEx' depth
          ( selectEVar ge,
            (fun acc' ->
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
                begin if it > 0 then searchEx (it - 1, depth) (ge', sc, acc')
                else raise (Error "not found")
                end
              else sc acc'
              end),
            acc )
      end

    let search (maxFill, ge, sc) = searchEx (1, maxFill) (ge, sc, [])
  end

  (* isInstantiated (V) = SOME(cid) or NONE
       where cid is the type family of the atomic target type of V,
       NONE if V is a kind or object or have variable type.
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

(* # 1 "src/meta/Uniquesearch.sml.ml" *)
