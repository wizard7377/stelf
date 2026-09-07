open! Stream.Stream_
open! Global.Global_
open! Intsyn.Lambda_
open! Names.Names_
open! Modes
open! Print.Print_
open! Typecheck.Typecheck_

(* # 1 "src/m2/MetaAbstract.sig.ml" *)
open Metasyn

(* Meta Abstraction *)
(* Author: Carsten Schuermann *)
include METAABSTRACT
(* signature METAABSTRACT *)

(* # 1 "src/m2/MetaAbstract.fun.ml" *)
open! Basis
open Metasyn
open MetaGlobal
open Modetable

(* Meta Abstraction *)
(* Author: Carsten Schuermann *)

exception Error of string

let () =
  Printexc.register_printer (function Error msg -> Some msg | _ -> None)

module MetaAbstract (MetaAbstract__0 : sig
  module Global : GLOBAL
  module MetaSyn : Metasyn.METASYN
  module MetaGlobal : METAGLOBAL.METAGLOBAL
  module Abstract : ABSTRACT

  (*! sharing Abstract.IntSyn = MetaSyn'.IntSyn !*)
  module ModeTable : Modetable.MODETABLE

  (*! sharing Modes.Modesyn.ModeSyn.IntSyn = MetaSyn'.IntSyn !*)
  module Whnf : WHNF

  (*! sharing Whnf.IntSyn = MetaSyn'.IntSyn !*)
  module Print : PRINT

  (*! sharing Print.IntSyn = MetaSyn'.IntSyn !*)
  module Constraints : CONSTRAINTS

  (*! sharing Constraints.IntSyn = MetaSyn'.IntSyn !*)
  module Unify : UNIFY

  (*! sharing Unify.IntSyn = MetaSyn'.IntSyn !*)
  module Names : NAMES

  (*! sharing Names.IntSyn = MetaSyn'.IntSyn !*)
  module TypeCheck : TYPECHECK

  (*! sharing TypeCheck.IntSyn = MetaSyn'.IntSyn !*)
  module Subordinate : Subordinate.Subordinate_.SUBORDINATE
end) : METAABSTRACT with module MetaSyn = MetaAbstract__0.MetaSyn = struct
  open MetaAbstract__0
  module MetaSyn = MetaAbstract__0.MetaSyn

  exception Error = Error

  open! struct
    module I = IntSyn
    module S = Stream
    module C = Constraints
    module M = Modes.Modesyn.ModeSyn

    type var = Ev of I.exp option ref * I.exp * MetaSyn.mode | Bv

    let checkEmpty = function
      | [] -> ()
      | cnstr ->
          Debug.msg' ~src:Debug.Group.meta ~level:Debug.Level.Debug
            Fmt.(
              const string "Number of constraints:"
              ++ (const int @@ List.length cnstr))
          @@ begin match C.simplify cnstr with
          | [] -> ()
          | _ -> raise (Error "Unresolved constraints")
          end

    let typecheck (MetaSyn.Prefix (g, m, b), v) =
      TypeCheck.typeCheck g (v, I.Uni I.Type)

    let modeEq = function
      | M.Marg (M.Plus, _), MetaSyn.Top -> true
      | M.Marg (M.Minus, _), MetaSyn.Bot -> true
      | _ -> false

    let rec atxLookup (a, r) = match a with
      | I.Null -> None
      | I.Decl (m, Bv) -> atxLookup (m, r)
      | I.Decl (m, (Ev (r', _, _) as e)) ->
          begin if r == r' then Some e else atxLookup (m, r)
          end

    let rec raiseType (depth, a, v) = match depth, a with
      | 0, g -> v
      | depth, I.Decl (g, d) ->
          raiseType (depth - 1, g, I.Pi ((d, I.Maybe), v))

    let rec weaken (depth, g, a) = match depth, g with
      | 0, g -> I.id
      | depth, I.Decl (g', (I.Dec (name, v) as d)) ->
          let w' = weaken (depth - 1, g', a) in
          begin if Subordinate.belowEq (I.targetFam v) a then I.dot1 w'
          else I.comp w' I.shift
          end

    let countPi v =
      let rec countPi' (a, n) = match a with
        | I.Root _ -> n
        | I.Pi (_, v) -> countPi' (v, n + 1)
        | I.EClo (v, _) -> countPi' (v, n)
      in
      countPi' (v, 0)

    let rec collectExp (lG0, g, us, mode, adepth) =
      collectExpW (lG0, g, Whnf.whnf us, mode, adepth)

    and collectExpW (lG0, g, a, mode, b) = match lG0, a, b with
      | lG0, (I.Uni _, s), adepth -> adepth
      | lG0, (I.Pi ((d, _), v), s), adepth ->
          collectExp
            ( lG0,
              I.Decl (g, I.decSub d s),
              (v, I.dot1 s),
              mode,
              collectDec (lG0, g, (d, s), mode, adepth) )
      | lG0, (I.Lam (d, u), s), adepth ->
          collectExp
            ( lG0,
              I.Decl (g, I.decSub d s),
              (u, I.dot1 s),
              mode,
              collectDec (lG0, g, (d, s), mode, adepth) )
      | lG0, ((I.Root (I.BVar k, s_), s) as us), ((a, depth) as adepth) ->
          let l = I.ctxLength g in
          begin if k = l + depth - lG0 && depth > 0 then
            let (I.Dec (_, v)) = I.ctxDec g k in
            collectSpine (lG0, g, (s_, s), mode, (I.Decl (a, Bv), depth - 1))
          else collectSpine (lG0, g, (s_, s), mode, adepth)
          end
      | lG0, (I.Root (c, s_), s), adepth ->
          collectSpine (lG0, g, (s_, s), mode, adepth)
      | lG0, (I.EVar (r, gx, v, cnstrs), s), ((a, depth) as adepth)
        ->
          begin match atxLookup (a, r) with
          | None ->
              ignore (checkEmpty !cnstrs);
              let lGp' = I.ctxLength gx - lG0 + depth in
              let w = weaken (lGp', gx, I.targetFam v) in
              let iw = Whnf.invert w in
              let gx' = Whnf.strengthen iw gx in
              let lGp'' = I.ctxLength gx' - lG0 + depth in
              let vraised = raiseType (lGp'', gx', I.EClo (v, iw)) in
              let (I.EVar (r', _, _, _) as x') =
                I.newEVar gx' (I.EClo (v, iw))
              in
              ignore (Unify.instantiateEVar r (I.EClo (x', w)) []);
              collectSub
                ( lG0,
                  g,
                  lGp'',
                  s,
                  mode,
                  (I.Decl (a, Ev (r', vraised, mode)), depth) )
          | Some (Ev (_, v, _)) ->
              let lGp' = countPi v in
              collectSub (lG0, g, lGp', s, mode, adepth)
          end
      | lGO, (I.FgnExp (csid, fge), s), adepth ->
          I.FgnExpStd.fold csid fge
            (function
              | u, adepth' -> collectExp (lGO, g, (u, s), mode, adepth'))
            adepth

    and collectSub (lG0, g, lG', a, mode, b) = match lG', a, b with
      | 0, _, adepth -> adepth
      | lG', I.Shift k, adepth ->
          collectSub
            (lG0, g, lG', I.Dot (I.Idx (k + 1), I.Shift (k + 1)), mode, adepth)
      | lG', I.Dot (I.Idx k, s), ((a, depth) as adepth) ->
          collectSub (lG0, g, lG' - 1, s, mode, adepth)
      | lG', I.Dot (I.Exp u, s), adepth ->
          collectSub
            ( lG0,
              g,
              lG' - 1,
              s,
              mode,
              collectExp (lG0, g, (u, I.id), mode, adepth) )

    and collectSpine (lG0, g, a, mode, adepth) = match a with
      | (I.Nil, _) -> adepth
      | (I.SClo (s_, s'), s) ->
          collectSpine (lG0, g, (s_, I.comp s' s), mode, adepth)
      | (I.App (u, s_), s) ->
          collectSpine
            (lG0, g, (s_, s), mode, collectExp (lG0, g, (u, s), mode, adepth))

    and collectDec (lG0, g, (I.Dec (x, v), s), mode, adepth) =
      collectExp (lG0, g, (v, s), mode, adepth)

    let collectModeW (lG0, g, modeIn, modeRec, a, adepth) = match a with
      | (I.Root (I.Const cid, s_), s) ->
          let rec collectModeW' (a, adepth) = match a with
            | ((I.Nil, _), M.Mnil) -> adepth
            | ((I.SClo (s_, s'), s), m) ->
                collectModeW' (((s_, I.comp s' s), m), adepth)
            | ((I.App (u, s_), s), M.Mapp (m, mS)) ->
                collectModeW'
                  ( ((s_, s), mS),
                    begin if modeEq (m, modeIn) then
                      collectExp (lG0, g, (u, s), modeRec, adepth)
                    else adepth
                    end )
          in
          let mS = valOf (ModeTable.modeLookup cid) in
          collectModeW' (((s_, s), mS), adepth)
      | (I.Pi ((d, p), v), s) ->
          raise
            (Error
               "Implementation restricted to the Horn fragment of the meta \
                logic")

    let rec collectG (lG0, g, vs, adepth) =
      collectGW (lG0, g, Whnf.whnf vs, adepth)

    and collectGW (lG0, g, vs, adepth) =
      collectModeW
        ( lG0,
          g,
          MetaSyn.Bot,
          MetaSyn.Top,
          vs,
          collectModeW (lG0, g, MetaSyn.Top, MetaSyn.Bot, vs, adepth) )

    let rec collectDTop (lG0, g, vs, adepth) =
      collectDTopW (lG0, g, Whnf.whnf vs, adepth)

    and collectDTopW (lG0, g, a, adepth) = match a with
      | (I.Pi (((I.Dec (x, v1) as d), No), v2), s) ->
          collectG
            ( lG0,
              g,
              (v1, s),
              collectDTop
                (lG0, I.Decl (g, I.decSub d s), (v2, I.dot1 s), adepth) )
      | ((I.Root _, s) as vs) ->
          collectModeW (lG0, g, MetaSyn.Top, MetaSyn.Top, vs, adepth)

    let rec collectDBot (lG0, g, vs, adepth) =
      collectDBotW (lG0, g, Whnf.whnf vs, adepth)

    and collectDBotW (lG0, g, a, adepth) = match a with
      | (I.Pi ((d, _), v), s) ->
          collectDBot
            (lG0, I.Decl (g, I.decSub d s), (v, I.dot1 s), adepth)
      | ((I.Root _, s) as vs) ->
          collectModeW (lG0, g, MetaSyn.Bot, MetaSyn.Bot, vs, adepth)

    let collect (MetaSyn.Prefix (g, m, b), v) =
      let lG0 = I.ctxLength g in
      let a, k =
        collectDBot
          (lG0, g, (v, I.id), collectDTop (lG0, g, (v, I.id), (I.Null, lG0)))
      in
      a

    let lookupEV (a_, r) =
      let rec lookupEV' (a, r', k) = match a with
        | I.Decl (a, Ev (r, v, _)) ->
            begin if r == r' then (k, v) else lookupEV' (a, r', k + 1)
            end
        | I.Decl (a, Bv) -> lookupEV' (a, r', k + 1)
      in
      lookupEV' (a_, r, 1)

    let lookupBV (a_, i) =
      let rec lookupBV' (a, i, k) = match a, i with
        | I.Decl (a, Ev (r, v, _)), i -> lookupBV' (a, i, k + 1)
        | I.Decl (a, Bv), 1 -> k
        | I.Decl (a, Bv), i -> lookupBV' (a, i - 1, k + 1)
      in
      lookupBV' (a_, i, 1)

    let rec abstractExpW (a_, g, depth, a) = match a with
      | ((I.Uni l as v), s) -> v
      | (I.Pi ((d, p), v), s) ->
          Abstract.piDepend
            (abstractDec (a_, g, depth, (d, s))) p (abstractExp
                (a_, I.Decl (g, I.decSub d s), depth + 1, (v, I.dot1 s)))
      | (I.Lam (d, u), s) ->
          I.Lam
            ( abstractDec (a_, g, depth, (d, s)),
              abstractExp
                (a_, I.Decl (g, I.decSub d s), depth + 1, (u, I.dot1 s))
            )
      | (I.Root ((I.BVar k as c), s_), s) ->
          begin if k > depth then
            let k' = lookupBV (a_, k - depth) in
            I.Root (I.BVar (k' + depth), abstractSpine (a_, g, depth, (s_, s)))
          else I.Root (c, abstractSpine (a_, g, depth, (s_, s)))
          end
      | (I.Root (c, s_), s) ->
          I.Root (c, abstractSpine (a_, g, depth, (s_, s)))
      | (I.EVar (r, _, v, _), s) ->
          let k, vraised = lookupEV (a_, r) in
          I.Root
            ( I.BVar (k + depth),
              abstractSub
                (a_, g, depth, (vraised, I.id), s, I.targetFam v, I.Nil) )
      | (I.FgnExp (csid, fge), s) ->
          I.FgnExpStd.Map.apply csid fge (function u ->
              abstractExp (a_, g, depth, (u, s)))

    and abstractExp (a, g, depth, us) =
      abstractExpW (a, g, depth, Whnf.whnf us)

    and abstractSpine (a_, g, depth, a) = match a with
      | (I.Nil, _) -> I.Nil
      | (I.App (u, s_), s) ->
          I.App
            ( abstractExp (a_, g, depth, (u, s)),
              abstractSpine (a_, g, depth, (s_, s)) )
      | (I.SClo (s_, s'), s) ->
          abstractSpine (a_, g, depth, (s_, I.comp s' s))

    and abstractSub (a, g, depth, xVt, s, b, s_) =
      abstractSubW (a, g, depth, Whnf.whnf xVt, s, b, s_)

    and abstractSubW (a_, g, depth, a, c, b, s_) = match a, c with
      | (I.Root _, _), s -> s_
      | ((I.Pi _, _) as xVt), I.Shift k ->
          abstractSub
            (a_, g, depth, xVt, I.Dot (I.Idx (k + 1), I.Shift (k + 1)), b, s_)
      | ((I.Pi (_, xv'), t) as xVt), I.Dot (I.Idx k, s) ->
          let (I.Dec (x, v)) = I.ctxDec g k in
          begin if k > depth then
            let k' = lookupBV (a_, k - depth) in
            abstractSub
              ( a_,
                g,
                depth,
                (xv', I.dot1 t),
                s,
                b,
                I.App (I.Root (I.BVar (k' + depth), I.Nil), s_) )
          else
            abstractSub
              ( a_,
                g,
                depth,
                (xv', I.dot1 t),
                s,
                b,
                I.App (I.Root (I.BVar k, I.Nil), s_) )
          end
      | ((I.Pi (_, xv'), t) as xVt), I.Dot (I.Exp u, s)
        ->
          abstractSub
            ( a_,
              g,
              depth,
              (xv', I.dot1 t),
              s,
              b,
              I.App (abstractExp (a_, g, depth, (u, I.id)), s_) )

    and abstractDec (a, g, depth, (I.Dec (xOpt, v), s)) =
      I.Dec (xOpt, abstractExp (a, g, depth, (v, s)))

    let rec abstractCtx = function
      | I.Null, (MetaSyn.Prefix (I.Null, I.Null, I.Null) as gm) -> (gm, I.Null)
      | ( I.Decl (a, Bv),
          MetaSyn.Prefix (I.Decl (g, d), I.Decl (m, marg), I.Decl (b_, b)) )
        ->
          let MetaSyn.Prefix (g', m', b'), lG' =
            abstractCtx (a, MetaSyn.Prefix (g, m, b_))
          in
          let d' = abstractDec (a, g, 0, (d, I.id)) in
          let (I.Dec (_, v)) = d' in
          ignore begin if !Global.doubleCheck then
              typecheck (MetaSyn.Prefix (g', m', b'), v)
            else ()
            end;
          ( MetaSyn.Prefix
              ( I.Decl (g', Names.decName g' d'),
                I.Decl (m', marg),
                I.Decl (b', b) ),
            I.Decl (lG', d') )
      | I.Decl (a, Ev (r, v, m)), gm ->
          let MetaSyn.Prefix (g', m', b'), lG' = abstractCtx (a, gm) in
          let v'' = abstractExp (a, lG', 0, (v, I.id)) in
          ignore begin if !Global.doubleCheck then
              typecheck (MetaSyn.Prefix (g', m', b'), v'')
            else ()
            end;
          ( MetaSyn.Prefix
              ( I.Decl (g', Names.decName g' (I.Dec (None, v''))),
                I.Decl (m', m),
                I.Decl
                  ( b',
                    begin match m with
                    | MetaSyn.Top -> !MetaGlobal.maxSplit
                    | MetaSyn.Bot -> 0
                    end ) ),
            lG' )

    let abstract
        (MetaSyn.State (name, (MetaSyn.Prefix (g, m, b) as gm), v) as s) =
      ignore (Names.varReset I.Null);
      let a = collect (gm, v) in
      let gm', _ = abstractCtx (a, gm) in
      let v' = abstractExp (a, g, 0, (v, I.id)) in
      let s = MetaSyn.State (name, gm', v') in
      ignore begin if !Global.doubleCheck then typecheck (gm', v') else ()
        end;
      s
  end

  (* Invariants? *)
  (* Definition: Mode dependency order

       A pair ((G, M), V) is in mode dependency order iff
           G |- V : type
           G |- M modes
       and G = G0+, G1-, G1+,  ... G0-
       and V = {xn:Vn} ..{x1:V1}P0
       where G0+ collects all +variables when traversing P0 in order
       and Gi+ collects all +variables when traverseing Vi in order  (i > 0)
       and Gi- collects all -variables when traversing Vi in order   (i > 0)
       and G0- collects all -variables when traversing P0 in Order.
    *)
  (* Variable found during collect  *)
  (* Var ::= EVar <r_, V, St>       *)
  (*       | BV                     *)
  (*--------------------------------------------------------------------*)
  (* First section: Collecting EVars and BVars in mode dependency order *)
  (*--------------------------------------------------------------------*)
  (* checkEmpty Cnstr = ()
       raises Error exception if constraints Cnstr cannot be simplified
       to the empty constraint
    *)
  (* Let G x A: defined as

       .      x .            = .
       (G, V) x (A, BVar)    = (G x A), V
       (G, V) x (A, EVar V') = (G, V x A), V'

       Then all A : Atx satisfy the following invariant: |- A Atx

       ? If    A = A', EV (r, V, m)
       ? then  . |- V = {G x A'}.V' : type
       ? where G x A' |- V' : type

       We write A ||- U if all EVars and BVars of U are collected in A,
       A ||- S if all EVars and BVars of S are collected in A,
       and similiar notation for the other syntactic categories.
    *)
  (* typecheck ((G, M), V) = ()

       Invariant:
       If G |- V : type
       then typecheck returns ()
       else TypeCheck.Error is raised
    *)
  (* modeEq (marg, st) = B'

       Invariant:
       If   (marg = + and st = top) or (marg = - and st = bot)
       then B' = true
       else B' = false
    *)
  (* atxLookup (atx, r)  = Eopt'

       Invariant:
       If   r exists in atx as EV (V)
       then Eopt' = SOME EV and . |- V : type
       else Eopt' = NONE
    *)
  (* raiseType (k, G, V) = {{G'}} V

       Invariant:
       If G |- V : L
          G = G0, G'  (so k <= |G|)
       then  G0 |- {{G'}} V : L
             |G'| = k

       All abstractions are potentially dependent.
    *)
  (* weaken (depth,  G, a) = (w')
    *)
  (* countPi V = n'

       If   G |- x : V
       and  V = {G'} V'
       then |G'| = n'
    *)
  (* V in nf or enf? -fp *)
  (* collectExp (lG0, G, (U, s), mode, (A, depth)) = (A', depth')
       collects EVar's and BVar's in mode dependency order!
       depth is needed to decide if a BVar is encountered for the first time.

       Invariant:
       Let A : auxiliary context,
           depth : length of the subcontext of G, which must still
                   be traversed and collected

       If   G  |- s : G'  and   G' |- U : V
       and  G = G0, G0', GO'', Gp
       and  . |- A Atx
       and  |G0,  G0', G0''| =  lG0
       and       |G0', G0''| = depth
       then           |G0''| = depth'
       and  . |- A' Atx
       and  A' = A, A''
       and  A'' ||- U [s]
    *)
  (* impossible? *)
  (* s = id *)
  (* invariant: all variables (EV or BV) in V already seen! *)
  (* lGp' >= 0 *)
  (* lGp'' >= 0 *)
  (* invariant: all variables (EV) in Vraised already seen *)
  (* hack - should discuss with cs    -rv *)
  (* collectSub (lG0, G, lG'', s, mode, (A, depth)) = (A', depth')
       collects EVar's and BVar's in mode dependency order!
       depth is needed to decide if a BVar is encountered for the first time.

       Invariant:
       Let A : auxiliary context,
           depth : length of the subcontext of G, which must still
                   be traversed and collected

       If   G  |- s : G'
       and  G = G0, G0', GO'', Gp
       and  . |- A Atx
       and  |G0,  G0', G0''| =  lG0
       and       |G0', G0''| = depth
       and  G' = GO, G''
       and  |G''| = lG''
       then           |G0''| = depth'
       and  . |- A' Atx
       and  A' = A, A''
       and  A'' ||- s   (for the first |G'| elements of s)
    *)
  (* eta expansion *)
  (* typing invariant guarantees that (EV, BV) in k : V already
             collected !! *)
  (* typing invariant guarantees that (EV, BV) in V already
             collected !! *)
  (* collectSpine (lG0, G, (S, s), mode, (A, depth)) = (A', depth')
       collects EVar's and BVar's in mode dependency order!
       depth is needed to decide if a BVar is encountered for the first time.

       Invariant:
       Let A : auxiliary context,
           depth : length of the subcontext of G, which must still
                   be traversed and collected

       If   G  |- s : G'  and   G' |- S : V > V'
       and  G = G0, G0', GO'', Gp
       and  . |- A Atx
       and  |G0,  G0', G0''| =  lG0
       and       |G0', G0''| = depth
       then           |G0''| = depth'
       and  . |- A' Atx
       and  A' = A, A''
       and  A'' ||- S
    *)
  (* collectDec (lG0, G, (x:D, s), mode, (A, depth)) = (A', depth')
       collects EVar's and BVar's in mode dependency order!
       depth is needed to decide if a BVar is encountered for the first time.

       Invariant:
       Let A : auxiliary context,
           depth : length of the subcontext of G, which must still
                   be traversed and collected

       If   G  |- s : G'  and   G' |- D : L
       and  G = G0, G0', GO'', Gp
       and  . |- A Atx
       and  |G0,  G0', G0''| =  lG0
       and       |G0', G0''| = depth
       then           |G0''| = depth'
       and  . |- A' Atx
       and  A' = A, A''
       and  A'' ||- x:D[s]
    *)
  (* collectModeW (lG0, G, modeIn, modeRec, (V, s) (A, depth)) = (A', depth')
       collects EVar's and BVar's in mode dependency order!
       depth is needed to decide if a BVar is encountered for the first time.

       Invariant:
       Let A : auxiliary context,
           depth : length of the subcontext of G, which must still
                   be traversed and collected

       If   G  |- s : G'  and   G' |- V : L        V[s] in whnf
       and  G = G0, G0', GO'', Gp
       and  . |- A Atx
       and  |G0,  G0', G0''| =  lG0
       and       |G0', G0''| = depth
       then           |G0''| = depth'
       and  . |- A' Atx
       and  A' = A, A''
       and  A'' ||- V
       and  A'' consists of all EVars/BVars marked with modeIn in V and
                recored as modeRec
    *)
  (* s = id *)
  (* collectG (lG0, G, (V, s) (A, depth)) = (A', depth')
       collects EVar's and BVar's in mode dependency order!
       depth is needed to decide if a BVar is encountered for the first time.

       Invariant:
       Let A : auxiliary context,
           depth : length of the subcontext of G, which must still
                   be traversed and collected

       If   G  |- s : G'  and   G' |- V : L
       and  G = G0, G0', GO'', Gp
       and  . |- A Atx
       and  |G0,  G0', G0''| =  lG0
       and       |G0', G0''| = depth
       then           |G0''| = depth'
       and  . |- A' Atx
       and  A' = A, A''
       and  A'' ||- V
       and  A'' consists of all Top EVars/BVars in the head of V
                    followed by Bot/Top EVars/BVars of recursive calls
                    (A'' is in mode dependecy order)
    *)
  (* collectDTop (lG0, G, (V, s) (A, depth)) = (A', depth')
       collects EVar's and BVar's in mode dependency order!
       depth is needed to decide if a BVar is encountered for the first time.

       Invariant:
       Let A : auxiliary context,
           depth : length of the subcontext of G, which must still
                   be traversed and collected

       If   G  |- s : G'  and   G' |- V : L
       and  G = G0, G0', GO'', Gp
       and  . |- A Atx
       and  |G0,  G0', G0''| =  lG0
       and       |G0', G0''| = depth
       then           |G0''| = depth'
       and  . |- A' Atx
       and  A' = A, A''
       and  A'' ||- V
       and  A'' consists of all Top EVars/BVars in the head of V
                    followed by Bot/Top EVars/BVars of recursive calls
                    (A'' is in mode dependecy order)
    *)
  (* only arrows *)
  (* s = id *)
  (* collectDBot (lG0, G, (V, s), (A, depth)) = (A', depth')
       collects EVar's and BVar's in mode dependency order!
       depth is needed to decide if a BVar is encountered for the first time.

       Invariant:
       Let A : auxiliary context,
           depth : length of the subcontext of G, which must still
                   be traversed and collected

       If   G  |- s : G'  and   G' |- V : L
       and  G = G0, G0', GO'', Gp
       and  . |- A Atx
       and  |G0,  G0', G0''| =  lG0
       and       |G0', G0''| = depth
       then           |G0''| = depth'
       and  . |- A' Atx
       and  A' = A, A''
       and  A'' ||- V
       and  A'' consists of all Top EVars/BVars in the head of V
                    followed by Bot/Top EVars/BVars of recursive calls
                    followed by Top EVars/BVars in the head of V
                    (A'' is in mode dependecy order)
    *)
  (* s = id *)
  (* collect ((G,_,_), V) = A'
       collects EVar's and BVar's in V mode dependency Order.

       Invariant:
       If   G  |- s : G'  and   G' |- V : L
       then . |- A' Atx
       and  A' = A, A''
       and  A'' ||- V
       and  A'' consists of all Top EVars/BVars in the head of V
                    followed by Bot/Top EVars/BVars of recursive calls
                    followed by Top EVars/BVars in the head of V
                    (A'' is in mode dependecy order)
    *)
  (*------------------------------------------------------------*)
  (* Second section: Abstracting over EVars and BVars that have *)
  (* been collected in mode dependency order                    *)
  (*------------------------------------------------------------*)
  (* lookupEV (A, r) = (k', V')

       Invariant:

       If   A ||- V
       and  G |- X : V' occuring in V
       then G x A |- k : V'
       and  . |- V' : type
    *)
  (* lookupEV' I.Null cannot occur by invariant *)
  (* lookupBV (A, i) = k'

       Invariant:

       If   A ||- V
       and  G |- V type
       and  G [x] A |- i : V'
       then ex a substititution  G x A |- s : G [x] A
       and  G x A |- k' : V''
       and  G x A |- V' [s] = V'' : type
    *)
  (* lookupBV' I.Null cannot occur by invariant *)
  (* abstractExpW (A, G, depth, (U, s)) = U'

       Invariant:
       If    G0, G |- s : G1   G1 |- U : V    (U,s) in whnf
       and   |G| = depth
       and   A is auxiliary context in mode dependency order
       and   A ||- U  and  A ||- V
       then  G0 x A, G |- U' : V'
       and   . ||- U' and . ||- V'
       and   U' is in nf
    *)
  (* s = id *)
  (* s = id *)
  (* IMPROVE: remove the raised variable, replace by V -cs ?-fp *)
  (* hack - should discuss with cs     -rv *)
  (* abstractExp, same as abstractExpW, but (V, s) need not be in whnf *)
  (* abstractSpine (A, G, depth, (S, s)) = U'

       Invariant:
       If    G0, G |- s : G1   G1 |- S : V1 > V2
       and   |G| = depth
       and   A is auxiliary context in mode dependency order
       and   A ||- U  and  H ||- V1
       then  G0 x A, G |- S' : V1' > V2'
       and   . ||- S' and . ||- V1'
    *)
  (* abstractSub (A, G, depth, (XV, t), s, b, S) = S'

       Invariant:
       If    G0, G |- s : G'
       and   |G| = depth
       and   A is auxiliary context in mode dependency order
       and   A ||- s
       then  G0 x A, G |- S' : {XV [t]}.W > W
       and   . ||- S'
    *)
  (* optimize: whnf not necessary *)
  (* abstractDec (A, G, depth, (x:V, s)) = x:V'

       Invariant:
       If    G0, G |- s : G1   G1 |- V : L
       and   |G| = G
       and   |G| = depth
       and   A is auxiliary context in mode dependency order
       and   A ||- V
       then  G0 x A, G |- V' : L
       and   . ||- V'
    *)
  (* abstractCtx (A, (G, M)) = ((G', M') , G'')

       Let E be a list of EVars possibly occuring in G

       Invariant:
       G' = G x A
       M' = M x A    (similar to G x A, but just represents mode information)
       G'' = G [x] A
    *)
  (* abstract ((G, M), V) = ((G', M') , V')

       Invariant:
       If    G |- V : type    (M modes associated with G)
       then  G' |- V' : type  (M' modes associated with G')
       and   . ||- V'
    *)
  let abstract = abstract
end
(*! sharing Subordinate.IntSyn = MetaSyn'.IntSyn  !*)
(* local *)
(* functor MetaAbstract *)

(* # 1 "src/m2/MetaAbstract.sml.ml" *)
