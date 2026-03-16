(* # 1 "src/m2/search.sig.ml" *)
open! Basis
open Metasyn

(* Basic search engine *)
(* Author: Carsten Schuermann *)
module type OLDSEARCH = sig
  module MetaSyn : METASYN

  exception Error of string

  val searchEx :
    IntSyn.dctx
    * IntSyn.exp list
    * (IntSyn.exp * IntSyn.sub)
    * (unit -> MetaSyn.state) ->
    MetaSyn.state list

  val searchAll :
    IntSyn.dctx
    * IntSyn.exp list
    * (IntSyn.exp * IntSyn.sub)
    * (MetaSyn.state list -> MetaSyn.state list) ->
    MetaSyn.state list
end
(* signature SEARCH *)

(* # 1 "src/m2/search.fun.ml" *)
open! Basis
open Metasyn
open Meta_global

(* Search (based on abstract machine ) *)
(* Author: Carsten Schuermann *)
module OLDSearch (OLDSearch__0 : sig
  (*! structure IntSyn' : INTSYN !*)
  module MetaGlobal : METAGLOBAL
  module MetaSyn' : METASYN

  (*! sharing MetaSyn'.IntSyn = IntSyn' !*)
  (*! structure CompSyn' : COMPSYN !*)
  (*! sharing CompSyn'.IntSyn = IntSyn' !*)
  module Whnf : WHNF

  (*! sharing Whnf.IntSyn = IntSyn' !*)
  module Unify : UNIFY

  (*! sharing Unify.IntSyn = IntSyn' !*)
  (*
                structure Assign : ASSIGN
                sharing Assign.IntSyn = IntSyn'
                *)
  module Index : INDEX

  (*! sharing Index.IntSyn = IntSyn' !*)
  module Compile : COMPILE

  (*! sharing Compile.IntSyn = IntSyn' !*)
  (*! sharing Compile.CompSyn = CompSyn' !*)
  module CPrint : CPRINT

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
  exception Error of string

  open! struct
    module I = IntSyn
    module M = MetaSyn
    module C = CompSyn.CompSyn

    let rec cidFromHead = function
      | I.Const a -> a
      | I.Def a -> a
      | I.Skonst a -> a

    let rec eqHead = function
      | I.Const a, I.Const a' -> a = a'
      | I.Def a, I.Def a' -> a = a'
      | _ -> false

    let rec solve = function
      | (C.Atom p, s), dp, sc, acck -> matchAtom ((p, s), dp, sc, acck)
      | (C.Impl (r, a_, h_, g), s), C.DProg (g_, dPool), sc, acck ->
          let d'_ = I.Dec (None, I.EClo (a_, s)) in
          solve
            ( (g, I.dot1 s),
              C.DProg (I.Decl (g_, d'_), I.Decl (dPool, C.Dec (r, s, h_))),
              (function m_, acck' -> sc (I.Lam (d'_, m_), acck')),
              acck )
      | (C.All (d_, g), s), C.DProg (g_, dPool), sc, acck ->
          let d'_ = I.decSub (d_, s) in
          solve
            ( (g, I.dot1 s),
              C.DProg (I.Decl (g_, d'_), I.Decl (dPool, C.Parameter)),
              (function m_, acck' -> sc (I.Lam (d'_, m_), acck')),
              acck )

    and rSolve = function
      | ps', (C.Eq q_, s), C.DProg (g_, dPool), sc, ((acc, k) as acck) -> begin
          if Unify.unifiable (g_, ps', (q_, s)) then sc (I.Nil, acck) else acc
        end
      | ps', (C.And (r, a_, g), s), (C.DProg (g_, dPool) as dp), sc, acck ->
          let x_ = I.newEVar (g_, I.EClo (a_, s)) in
          rSolve
            ( ps',
              (r, I.Dot (I.Exp x_, s)),
              dp,
              (function
              | s_, acck' ->
                  solve
                    ( (g, s),
                      dp,
                      (function
                      | m_, acck'' -> (
                          try
                            begin
                              Unify.unify (g_, (x_, I.id), (m_, I.id));
                              sc (I.App (m_, s_), acck'')
                            end
                          with Unify.Unify _ -> fst acck')),
                      acck )),
              acck )
      | ( ps',
          (C.Exists (I.Dec (_, a_), r), s),
          (C.DProg (g_, dPool) as dp),
          sc,
          acck ) ->
          let x_ = I.newEVar (g_, I.EClo (a_, s)) in
          rSolve
            ( ps',
              (r, I.Dot (I.Exp x_, s)),
              dp,
              (function s_, acck' -> sc (I.App (x_, s_), acck')),
              acck )

    and aSolve ((trivial_, s), dp, sc, acc) = sc ()

    and matchAtom
        ( ((I.Root (ha_, _), _) as ps'),
          (C.DProg (g_, dPool) as dp),
          sc,
          (acc, k) ) =
      let rec matchSig acc' =
        let rec matchSig' = function
          | [], acc'' -> acc''
          | hc_ :: sgn', acc'' ->
              let (C.SClause r) = C.sProgLookup (cidFromHead hc_) in
              let acc''' =
                Cs_manager.trail (function () ->
                    rSolve
                      ( ps',
                        (r, I.id),
                        dp,
                        (function s_, acck' -> sc (I.Root (hc_, s_), acck')),
                        (acc'', k - 1) ))
              in
              matchSig' (sgn', acc''')
        in
        matchSig' (Index.lookup (cidFromHead ha_), acc')
      in
      let rec matchDProg = function
        | null_, _, acc' -> matchSig acc'
        | I.Decl (dPool', C.Dec (r, s, ha'_)), n, acc' -> begin
            if eqHead (ha_, ha'_) then
              let acc'' =
                Cs_manager.trail (function () ->
                    rSolve
                      ( ps',
                        (r, I.comp (s, I.Shift n)),
                        dp,
                        (function
                        | s_, acck' -> sc (I.Root (I.BVar n, s_), acck')),
                        (acc', k - 1) ))
              in
              matchDProg (dPool', n + 1, acc'')
            else matchDProg (dPool', n + 1, acc')
          end
        | I.Decl (dPool', parameter_), n, acc' ->
            matchDProg (dPool', n + 1, acc')
      in
      begin if k < 0 then acc else matchDProg (dPool, 1, acc)
      end

    let rec occursInExp (r, vs_) = occursInExpW (r, Whnf.whnf vs_)

    and occursInExpW = function
      | r, (I.Uni _, _) -> false
      | r, (I.Pi ((d_, _), v_), s) ->
          occursInDec (r, (d_, s)) || occursInExp (r, (v_, I.dot1 s))
      | r, (I.Root (_, s_), s) -> occursInSpine (r, (s_, s))
      | r, (I.Lam (d_, v_), s) ->
          occursInDec (r, (d_, s)) || occursInExp (r, (v_, I.dot1 s))
      | r, (I.EVar (r', _, v'_, _), s) -> r = r' || occursInExp (r, (v'_, s))
      | r, (I.FgnExp (csid_, fge_), s) ->
          I.FgnExpStd.fold (csid_, fge_)
            (function u_, b_ -> b_ || occursInExp (r, (u_, s)))
            false

    and occursInSpine = function
      | _, (nil_, _) -> false
      | r, (I.SClo (s_, s'), s) -> occursInSpine (r, (s_, I.comp (s', s)))
      | r, (I.App (u_, s_), s) ->
          occursInExp (r, (u_, s)) || occursInSpine (r, (s_, s))

    and occursInDec (r, (I.Dec (_, v_), s)) = occursInExp (r, (v_, s))

    let rec nonIndex = function
      | _, [] -> true
      | r, I.EVar (_, _, v_, _) :: ge_ ->
          (not (occursInExp (r, (v_, I.id)))) && nonIndex (r, ge_)

    let rec selectEVar = function
      | [], _, acc -> acc
      | (I.EVar (r, _, _, _) as x_) :: ge_, vs_, acc -> begin
          if occursInExp (r, vs_) && nonIndex (r, acc) then
            selectEVar (ge_, vs_, x_ :: acc)
          else selectEVar (ge_, vs_, acc)
        end

    let rec searchEx' arg__1 arg__2 =
      begin match (arg__1, arg__2) with
      | max, ([], sc) -> [ sc () ]
      | max, (I.EVar (r, g_, v_, _) :: ge_, sc) ->
          solve
            ( (Compile.compileGoal (g_, v_), I.id),
              Compile.compileCtx false g_,
              (function
              | u'_, (acc', _) -> begin
                  Unify.instantiateEVar (r, u'_, []);
                  searchEx' max (ge_, sc)
                end),
              ([], max) )
      end

    let rec deepen f p_ =
      let rec deepen' (level, acc) =
        begin if level > !MetaGlobal.maxFill then acc
        else begin
          begin if !Global.chatter > 5 then print "#" else ()
          end;
          deepen' (level + 1, f level p_)
        end
        end
      in
      deepen' (1, [])

    let rec searchEx (g_, ge_, vs_, sc) =
      begin
        begin if !Global.chatter > 5 then print "[Search: " else ()
        end;
        let results =
          deepen searchEx'
            (selectEVar (ge_, vs_, []), function params_ -> sc params_)
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

    let rec searchAll' = function
      | [], acc, sc -> sc acc
      | I.EVar (r, g_, v_, _) :: ge_, acc, sc ->
          solve
            ( (Compile.compileGoal (g_, v_), I.id),
              Compile.compileCtx false g_,
              (function
              | u'_, (acc', _) -> begin
                  Unify.instantiateEVar (r, u'_, []);
                  searchAll' (ge_, acc', sc)
                end),
              (acc, !MetaGlobal.maxFill) )

    let rec searchAll (g_, ge_, vs_, sc) =
      searchAll' (selectEVar (ge_, vs_, []), [], sc)
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
(*! structure Cs_manager : CS_MANAGER !*)
(*! sharing Cs_manager.IntSyn = IntSyn' !*)
(* local ... *)
(* functor Search *)

(* # 1 "src/m2/search.sml.ml" *)
