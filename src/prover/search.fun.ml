open! Basis

(* Search (based on abstract machine ) : Version 1.3 *)
(* Author: Carsten Schuermann *)
module Search (Search__0 : sig
  module Global : GLOBAL

  (*! structure IntSyn' : INTSYN !*)
  (*! structure Tomega' : TOMEGA !*)
  (*! sharing Tomega'.IntSyn = IntSyn' !*)
  module State' : STATE

  (*! sharing State'.IntSyn = IntSyn' !*)
  (*! sharing State'.Tomega = Tomega' !*)
  module Abstract : ABSTRACT

  (*! sharing Abstract.IntSyn = IntSyn' !*)
  (*! sharing Abstract.Tomega = Tomega' !*)
  module Data : DATA
  module CompSyn' : COMPSYN

  (*! sharing CompSyn'.IntSyn = IntSyn' !*)
  module Whnf : WHNF

  (*! sharing Whnf.IntSyn = IntSyn' !*)
  module Unify : UNIFY

  (*! sharing Unify.IntSyn = IntSyn' !*)
  module Assign : ASSIGN

  (*! sharing Assign.IntSyn = IntSyn' !*)
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

  (*! sharing Names.IntSyn = IntSyn' !*)
  module Cs_manager : CS_MANAGER
end) : SEARCH = struct
  (*! structure IntSyn = IntSyn' !*)
  (*! structure Tomega = Tomega' !*)
  module State = State'

  (*! structure CompSyn = CompSyn' !*)
  exception Error of string

  open! struct
    module I = IntSyn
    module C = CompSyn

    let rec isInstantiated = function
      | I.Root (I.Const cid, _) -> true
      | I.Pi (_, v_) -> isInstantiated v_
      | I.Root (I.Def cid, _) -> true
      | I.Redex (v_, s_) -> isInstantiated v_
      | I.Lam (_, v_) -> isInstantiated v_
      | I.EVar ({ contents = Some v_ }, _, _, _) -> isInstantiated v_
      | I.EClo (v_, s) -> isInstantiated v_
      | _ -> false

    let rec compose' = function
      | null_, g_ -> g_
      | IntSyn.Decl (g_, d_), g'_ -> IntSyn.Decl (compose' (g_, g'_), d_)

    let rec shift = function
      | null_, s -> s
      | IntSyn.Decl (g_, d_), s -> I.dot1 (shift (g_, s))

    let rec exists p_ k_ =
      let rec exists' = function
        | null_ -> false
        | I.Decl (k'_, y_) -> p_ y_ || exists' k'_
      in
      exists' k_

    let rec occursInExp (r, vs_) = occursInExpW (r, Whnf.whnf vs_)

    and occursInExpW = function
      | r, (I.Uni _, _) -> false
      | r, (I.Pi ((d_, _), v_), s) ->
          occursInDec (r, (d_, s)) || occursInExp (r, (v_, I.dot1 s))
      | r, (I.Root (_, s_), s) -> occursInSpine (r, (s_, s))
      | r, (I.Lam (d_, v_), s) ->
          occursInDec (r, (d_, s)) || occursInExp (r, (v_, I.dot1 s))
      | r, (I.EVar (r', _, v'_, _), s) -> r = r' || occursInExp (r, (v'_, s))

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
      | [] -> []
      | (I.EVar (r, _, _, { contents = [] }) as x_) :: ge_ ->
          let xs_ = selectEVar ge_ in
          begin if nonIndex (r, xs_) then xs_ @ [ x_ ] else xs_
          end
      | (I.EVar (r, _, _, cnstrs) as x_) :: ge_ ->
          let xs_ = selectEVar ge_ in
          begin if nonIndex (r, xs_) then x_ :: xs_ else xs_
          end

    let rec pruneCtx = function
      | g_, 0 -> g_
      | I.Decl (g_, _), n -> pruneCtx (g_, n - 1)

    let rec cidFromHead = function
      | I.Const a -> a
      | I.Def a -> a
      | I.Skonst a -> a

    let rec eqHead = function
      | I.Const a, I.Const a' -> a = a'
      | I.Def a, I.Def a' -> a = a'
      | _ -> false

    let rec solve = function
      | max, depth, (C.Atom p, s), dp, sc ->
          matchAtom (max, depth, (p, s), dp, sc)
      | max, depth, (C.Impl (r, a_, ha_, g), s), C.DProg (g_, dPool), sc ->
          let d'_ = I.Dec (None, I.EClo (a_, s)) in
          Solve_
            ( max,
              depth + 1,
              (g, I.dot1 s),
              C.DProg (I.Decl (g_, d'_), I.Decl (dPool, C.Dec (r, s, ha_))),
              function m_ -> sc (I.Lam (d'_, m_)) )
      | max, depth, (C.All (d_, g), s), C.DProg (g_, dPool), sc ->
          let d'_ = I.decSub (d_, s) in
          Solve_
            ( max,
              depth + 1,
              (g, I.dot1 s),
              C.DProg (I.Decl (g_, d'_), I.Decl (dPool, C.parameter_)),
              function m_ -> sc (I.Lam (d'_, m_)) )

    and rSolve = function
      | max, depth, ps', (C.Eq q_, s), C.DProg (g_, dPool), sc -> begin
          if Unify.unifiable (g_, ps', (q_, s)) then sc I.nil_ else ()
        end
      | ( max,
          depth,
          ps',
          (C.Assign (q_, eqns), s),
          (C.DProg (g_, dPool) as dp),
          sc ) -> begin
          match Assign.assignable (g_, ps', (q_, s)) with
          | Some cnstr ->
              aSolve ((eqns, s), dp, cnstr, function () -> sc I.nil_)
          | None -> ()
        end
      | max, depth, ps', (C.And (r, a_, g), s), (C.DProg (g_, dPool) as dp), sc
        ->
          let x_ = I.newEVar (g_, I.EClo (a_, s)) in
          rSolve
            ( max,
              depth,
              ps',
              (r, I.Dot (I.Exp x_, s)),
              dp,
              function
              | s_ ->
                  Solve_
                    ( max,
                      depth,
                      (g, s),
                      dp,
                      function m_ -> sc (I.App (m_, s_)) ) )
      | max, depth, ps', (C.In (r, a_, g), s), (C.DProg (g_, dPool) as dp), sc
        ->
          let g0_ = pruneCtx (g_, depth) in
          let dPool0 = pruneCtx (dPool, depth) in
          let w = I.Shift depth in
          let iw = Whnf.invert w in
          let s' = I.comp (s, iw) in
          let x_ = I.newEVar (g0_, I.EClo (a_, s')) in
          let x'_ = I.EClo (x_, w) in
          rSolve
            ( max,
              depth,
              ps',
              (r, I.Dot (I.Exp x'_, s)),
              dp,
              function
              | s_ -> begin
                  if isInstantiated x_ then sc (I.App (x'_, s_))
                  else
                    Solve_
                      ( max,
                        0,
                        (g, s'),
                        C.DProg (g0_, dPool0),
                        function
                        | m_ -> (
                            try
                              begin
                                Unify.unify (g0_, (x_, I.id), (m_, I.id));
                                sc (I.App (I.EClo (m_, w), s_))
                              end
                            with Unify.Unify _ -> ()) )
                end )
      | ( max,
          depth,
          ps',
          (C.Exists (I.Dec (_, a_), r), s),
          (C.DProg (g_, dPool) as dp),
          sc ) ->
          let x_ = I.newEVar (g_, I.EClo (a_, s)) in
          rSolve
            ( max,
              depth,
              ps',
              (r, I.Dot (I.Exp x_, s)),
              dp,
              function s_ -> sc (I.App (x_, s_)) )
      | ( max,
          depth,
          ps',
          (C.Axists (I.ADec (Some x_, d), r), s),
          (C.DProg (g_, dPool) as dp),
          sc ) ->
          let x'_ = I.newAVar () in
          rSolve
            ( max,
              depth,
              ps',
              (r, I.Dot (I.Exp (I.EClo (x'_, I.Shift (-d))), s)),
              dp,
              sc )

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

    and matchAtom = function
      | 0, _, _, _, _ -> ()
      | ( max,
          depth,
          ((I.Root (ha_, _), _) as ps'),
          (C.DProg (g_, dPool) as dp),
          sc ) ->
          let rec matchSig' = function
            | [] -> ()
            | hc_ :: sgn' ->
                let (C.SClause r) = C.sProgLookup (cidFromHead hc_) in
                let _ =
                  Cs_manager.trail (function () ->
                      rSolve
                        ( max - 1,
                          depth,
                          ps',
                          (r, I.id),
                          dp,
                          function s_ -> sc (I.Root (hc_, s_)) ))
                in
                matchSig' sgn'
          in
          let rec matchBlock = function
            | [], (n, i) -> ()
            | (r, s, h'_) :: rGs'_, (n, i) -> begin
                if eqHead (ha_, h'_) then
                  let _ =
                    Cs_manager.trail (function () ->
                        rSolve
                          ( max - 1,
                            depth,
                            ps',
                            (r, I.comp (s, I.Shift n)),
                            dp,
                            function
                            | s_ -> sc (I.Root (I.Proj (I.Bidx n, i), s_)) ))
                  in
                  matchBlock (rGs'_, (n, i + 1))
                else matchBlock (rGs'_, (n, i + 1))
              end
          in
          let rec matchDProg = function
            | null_, _ -> matchSig' (Index.lookup (cidFromHead ha_))
            | I.Decl (dPool', C.Dec (r, s, ha'_)), n -> begin
                if eqHead (ha_, ha'_) then
                  let _ =
                    Cs_manager.trail (function () ->
                        rSolve
                          ( max - 1,
                            depth,
                            ps',
                            (r, I.comp (s, I.Shift n)),
                            dp,
                            function s_ -> sc (I.Root (I.BVar n, s_)) ))
                  in
                  matchDProg (dPool', n + 1)
                else matchDProg (dPool', n + 1)
              end
            | I.Decl (dPool', parameter_), n -> matchDProg (dPool', n + 1)
            | I.Decl (dPool', C.BDec rGs_), n -> begin
                matchBlock (rGs_, (n, 1));
                matchDProg (dPool', n + 1)
              end
            | I.Decl (dPool', pDec_), n -> matchDProg (dPool', n + 1)
          in
          matchDProg (dPool, 1)

    and searchEx' arg__1 arg__2 =
      begin match (arg__1, arg__2) with
      | max, ([], sc) -> sc max
      | max, ((I.EVar (r, g_, v_, _) as x_) :: ge_, sc) ->
          Solve_
            ( max,
              0,
              (Compile.compileGoal (g_, v_), I.id),
              Compile.compileCtx false g_,
              function
              | u'_ -> (
                  try
                    begin
                      Unify.unify (g_, (x_, I.id), (u'_, I.id));
                      searchEx' max (ge_, sc)
                    end
                  with Unify.Unify _ -> ()) )
      end

    let rec deepen depth f p_ =
      let rec deepen' level =
        begin if level > depth then ()
        else begin
          begin if !Global.chatter > 5 then print "#" else ()
          end;
          begin
            f level p_;
            deepen' (level + 1)
          end
        end
        end
      in
      deepen' 1

    let rec searchEx (it, depth) (ge_, sc) =
      begin
        begin if !Global.chatter > 5 then print "[Search: " else ()
        end;
        begin
          deepen depth searchEx'
            ( selectEVar ge_,
              function
              | max -> begin
                  begin if !Global.chatter > 5 then print "OK]\n" else ()
                  end;
                  let ge'_ =
                    foldr
                      (function
                        | (I.EVar (_, g_, _, _) as x_), l_ ->
                            Abstract.collectEVars (g_, (x_, I.id), l_))
                      [] ge_
                  in
                  let gE' = List.length ge'_ in
                  begin if gE' > 0 then begin
                    if it > 0 then searchEx (it - 1, 1) (ge'_, sc) else ()
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

    let rec search (maxFill, ge_, sc) = searchEx (1, maxFill) (ge_, sc)
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
  (*      | occursInExpW (r, (I.FgnExp (cs, ops), s)) =
          occursInExp (r, (#toInternal(ops)(), s)) *)
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
  let searchEx = search
end
(*! sharing Cs_manager.IntSyn = IntSyn' !*)
(* local ... *)
(* functor Search *)
