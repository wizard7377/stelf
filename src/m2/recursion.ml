(* # 1 "src/m2/recursion.sig.ml" *)
open! Basis
open Metasyn

(* Recursion *)
(* Author: Carsten Schuermann *)
include Recursion_intf
(* signature RECURSION *)

(* # 1 "src/m2/recursion.fun.ml" *)
open! Lemma
open! Filling
open! Basis
open Metasyn
open Meta_global
open Modetable
open Meta_print
open Meta_abstract

(* Recursion *)
(* Author: Carsten Schuermann *)
(* See [Rohwedder,Pfenning ESOP'96] *)
module Recursion (Recursion__0 : sig
  module Global : GLOBAL
  module MetaGlobal : Meta_global.METAGLOBAL
  module MetaSyn' : Metasyn.METASYN
  module Whnf : WHNF

  (*! sharing Whnf.IntSyn = MetaSyn'.IntSyn !*)
  module Unify : UNIFY

  (*! sharing Unify.IntSyn = MetaSyn'.IntSyn !*)
  module Conv : CONV

  (*! sharing Conv.IntSyn = MetaSyn'.IntSyn !*)
  module Names : NAMES

  (*! sharing Names.IntSyn = MetaSyn'.IntSyn !*)
  module Subordinate : Subordinate.Subordinate_.SUBORDINATE

  (*! sharing Subordinate.IntSyn = MetaSyn'.IntSyn !*)
  module Print : PRINT

  (*! sharing Print.IntSyn = MetaSyn'.IntSyn !*)
  module Order : ORDER

  (*! sharing Order.IntSyn = MetaSyn'.IntSyn !*)
  module ModeTable : Modetable.MODETABLE

  (*! sharing Modes.Modesyn.ModeSyn.IntSyn = MetaSyn'.IntSyn !*)
  module Lemma : Lemma_intf.LEMMA with module MetaSyn = MetaSyn'
  module Filling : Filling_intf.FILLING with module MetaSyn = MetaSyn'
  module MetaPrint : Meta_print.METAPRINT with module MetaSyn = MetaSyn'
  module MetaAbstract : Meta_abstract.METAABSTRACT with module MetaSyn = MetaSyn'
  module Formatter : FORMATTER
end) : Recursion_intf.RECURSION with module MetaSyn = Recursion__0.MetaSyn' = struct
  open Recursion__0
  module MetaSyn = MetaSyn'

  exception Error of string

  type nonrec operator = MetaSyn.state

  open! struct
    module M = MetaSyn
    module I = IntSyn
    module O = Order
    module N = Names
    module F = Formatter

    type quantifier = Universal | Existential

    let rec vectorToString (g_, o_) =
      let rec fmtOrder = function
        | Order.Arg (us_, vs_) ->
            [
              F.string (Print.expToString (g_, I.EClo (fst us_, snd us_)));
              F.string ":";
              F.string (Print.expToString (g_, I.EClo (fst vs_, snd vs_)));
            ]
        | Order.Lex l_ -> [ F.string "{"; F.hVbox (fmtOrders l_); F.string "}" ]
        | Order.Simul l_ ->
            [ F.string "["; F.hVbox (fmtOrders l_); F.string "]" ]
      and fmtOrders = function
        | [] -> []
        | o_ :: [] -> fmtOrder o_
        | o_ :: l_ -> fmtOrder o_ @ (F.string " " :: fmtOrders l_)
      in
      F.makestring_fmt (F.hVbox (fmtOrder o_))

    let rec vector (c, (s_, s)) =
      let vid_ = (I.constType c, I.id) in
      let rec select' (n, (ss'_, vs''_)) = select'W (n, (ss'_, Whnf.whnf vs''_))
      and select'W = function
        | 1, ((I.App (u'_, s'_), s'), (I.Pi ((I.Dec (_, v''_), _), _), s'')) ->
            ((u'_, s'), (v''_, s''))
        | n, ((I.SClo (s'_, s1'), s2'), vs''_) ->
            select'W (n, ((s'_, I.comp (s1', s2')), vs''_))
        | n, ((I.App (u'_, s'_), s'), (I.Pi ((I.Dec (_, v1''_), _), v2''_), s''))
          ->
            select'
              ( n - 1,
                ((s'_, s'), (v2''_, I.Dot (I.Exp (I.EClo (u'_, s')), s''))) )
      in
      let rec select = function
        | O.Arg n -> O.Arg (select' (n, ((s_, s), vid_)))
        | O.Lex l_ -> O.Lex (map select l_)
        | O.Simul l_ -> O.Simul (map select l_)
      in
      select (O.selLookup c)

    let rec set_parameter (g_, (I.EVar (r, _, v_, _) as x_), k, sc, ops) =
      let rec set_parameter' = function
        | 0, ops' -> ops'
        | k', ops' ->
            let (I.Dec (_, v'_) as d'_) = I.ctxDec (g_, k') in
            let ops'' =
              Cs_manager.trail (function () ->
                  begin if
                    Unify.unifiable (g_, (v_, I.id), (v'_, I.id))
                    && Unify.unifiable
                         (g_, (x_, I.id), (I.Root (I.BVar k', I.Nil), I.id))
                  then sc ops'
                  else ops'
                  end)
            in
            set_parameter' (k' - 1, ops'')
      in
      set_parameter' (k, ops)

    let rec ltinit (g_, k, (us_, vs_), usVs'_, sc, ops) =
      ltinitW (g_, k, Whnf.whnfEta (us_, vs_), usVs'_, sc, ops)

    and ltinitW = function
      | g_, k, (us_, ((I.Root _, _) as vs_)), usVs'_, sc, ops ->
          lt (g_, k, (us_, vs_), usVs'_, sc, ops)
      | ( g_,
          k,
          ((I.Lam (d1_, u_), s1), (I.Pi (d2_, v_), s2)),
          ((u'_, s1'), (v'_, s2')),
          sc,
          ops ) ->
          ltinit
            ( I.Decl (g_, I.decSub (d1_, s1)),
              k + 1,
              ((u_, I.dot1 s1), (v_, I.dot1 s2)),
              ((u'_, I.comp (s1', I.shift)), (v'_, I.comp (s2', I.shift))),
              sc,
              ops )

    and lt (g_, k, (us_, vs_), (us'_, vs'_), sc, ops) =
      ltW (g_, k, (us_, vs_), Whnf.whnfEta (us'_, vs'_), sc, ops)

    and ltW = function
      | g_, k, (us_, vs_), ((I.Root (I.Const c, s'_), s'), vs'_), sc, ops ->
          ltSpine
            (g_, k, (us_, vs_), ((s'_, s'), (I.constType c, I.id)), sc, ops)
      | g_, k, (us_, vs_), ((I.Root (I.BVar n, s'_), s'), vs'_), sc, ops ->
        begin
          if n <= k then
            let (I.Dec (_, v'_)) = I.ctxDec (g_, n) in
            ltSpine (g_, k, (us_, vs_), ((s'_, s'), (v'_, I.id)), sc, ops)
          else ops
        end
      | g_, _, _, ((I.EVar _, _), _), _, ops -> ops
      | ( g_,
          k,
          ((u_, s1), (v_, s2)),
          ( (I.Lam ((I.Dec (_, v1'_) as d_), u'_), s1'),
            (I.Pi ((I.Dec (_, v2'_), _), v'_), s2') ),
          sc,
          ops ) -> begin
          if Subordinate.equiv (I.targetFam v_, I.targetFam v1'_) then
            let x_ = I.newEVar (g_, I.EClo (v1'_, s1')) in
            let sc' ops' = set_parameter (g_, x_, k, sc, ops') in
            lt
              ( g_,
                k,
                ((u_, s1), (v_, s2)),
                ((u'_, I.Dot (I.Exp x_, s1')), (v'_, I.Dot (I.Exp x_, s2'))),
                sc',
                ops )
          else begin
            if Subordinate.below (I.targetFam v1'_, I.targetFam v_) then
              let x_ = I.newEVar (g_, I.EClo (v1'_, s1')) in
              lt
                ( g_,
                  k,
                  ((u_, s1), (v_, s2)),
                  ((u'_, I.Dot (I.Exp x_, s1')), (v'_, I.Dot (I.Exp x_, s2'))),
                  sc,
                  ops )
            else ops
          end
        end

    and ltSpine (g_, k, (us_, vs_), (ss'_, vs'_), sc, ops) =
      ltSpineW (g_, k, (us_, vs_), (ss'_, Whnf.whnf vs'_), sc, ops)

    and ltSpineW = function
      | g_, k, (us_, vs_), ((I.Nil, _), _), _, ops -> ops
      | g_, k, (us_, vs_), ((I.SClo (s_, s'), s''), vs'_), sc, ops ->
          ltSpineW (g_, k, (us_, vs_), ((s_, I.comp (s', s'')), vs'_), sc, ops)
      | ( g_,
          k,
          (us_, vs_),
          ((I.App (u'_, s'_), s1'), (I.Pi ((I.Dec (_, v1'_), _), v2'_), s2')),
          sc,
          ops ) ->
          let ops' =
            le (g_, k, (us_, vs_), ((u'_, s1'), (v1'_, s2')), sc, ops)
          in
          ltSpine
            ( g_,
              k,
              (us_, vs_),
              ((s'_, s1'), (v2'_, I.Dot (I.Exp (I.EClo (u'_, s1')), s2'))),
              sc,
              ops' )

    and eq (g_, (us_, vs_), (us'_, vs'_), sc, ops) =
      Cs_manager.trail (function () ->
          begin if
            Unify.unifiable (g_, vs_, vs'_) && Unify.unifiable (g_, us_, us'_)
          then sc ops
          else ops
          end)

    and le (g_, k, (us_, vs_), (us'_, vs'_), sc, ops) =
      let ops' = eq (g_, (us_, vs_), (us'_, vs'_), sc, ops) in
      leW (g_, k, (us_, vs_), Whnf.whnfEta (us'_, vs'_), sc, ops')

    and leW = function
      | ( g_,
          k,
          ((u_, s1), (v_, s2)),
          ( (I.Lam ((I.Dec (_, v1'_) as d_), u'_), s1'),
            (I.Pi ((I.Dec (_, v2'_), _), v'_), s2') ),
          sc,
          ops ) -> begin
          if Subordinate.equiv (I.targetFam v_, I.targetFam v1'_) then
            let x_ = I.newEVar (g_, I.EClo (v1'_, s1')) in
            let sc' ops' = set_parameter (g_, x_, k, sc, ops') in
            le
              ( g_,
                k,
                ((u_, s1), (v_, s2)),
                ((u'_, I.Dot (I.Exp x_, s1')), (v'_, I.Dot (I.Exp x_, s2'))),
                sc',
                ops )
          else begin
            if Subordinate.below (I.targetFam v1'_, I.targetFam v_) then
              let x_ = I.newEVar (g_, I.EClo (v1'_, s1')) in
              le
                ( g_,
                  k,
                  ((u_, s1), (v_, s2)),
                  ((u'_, I.Dot (I.Exp x_, s1')), (v'_, I.Dot (I.Exp x_, s2'))),
                  sc,
                  ops )
            else ops
          end
        end
      | g_, k, (us_, vs_), (us'_, vs'_), sc, ops ->
          lt (g_, k, (us_, vs_), (us'_, vs'_), sc, ops)

    let rec ordlt = function
      | g_, O.Arg usVs_, O.Arg usVs'_, sc, ops ->
          ltinit (g_, 0, usVs_, usVs'_, sc, ops)
      | g_, O.Lex l_, O.Lex l'_, sc, ops -> ordltLex (g_, l_, l'_, sc, ops)
      | g_, O.Simul l_, O.Simul l'_, sc, ops -> ordltSimul (g_, l_, l'_, sc, ops)

    and ordltLex = function
      | g_, [], [], sc, ops -> ops
      | g_, o_ :: l_, o'_ :: l'_, sc, ops ->
          let ops' =
            Cs_manager.trail (function () -> ordlt (g_, o_, o'_, sc, ops))
          in
          ordeq
            ( g_,
              o_,
              o'_,
              (function ops'' -> ordltLex (g_, l_, l'_, sc, ops'')),
              ops' )

    and ordltSimul = function
      | g_, [], [], sc, ops -> ops
      | g_, o_ :: l_, o'_ :: l'_, sc, ops ->
          let ops'' =
            Cs_manager.trail (function () ->
                ordlt
                  ( g_,
                    o_,
                    o'_,
                    (function ops' -> ordleSimul (g_, l_, l'_, sc, ops')),
                    ops ))
          in
          ordeq
            ( g_,
              o_,
              o'_,
              (function ops' -> ordltSimul (g_, l_, l'_, sc, ops')),
              ops'' )

    and ordleSimul = function
      | g_, [], [], sc, ops -> sc ops
      | g_, o_ :: l_, o'_ :: l'_, sc, ops ->
          ordle
            ( g_,
              o_,
              o'_,
              (function ops' -> ordleSimul (g_, l_, l'_, sc, ops')),
              ops )

    and ordeq = function
      | g_, O.Arg (us_, vs_), O.Arg (us'_, vs'_), sc, ops -> begin
          if Unify.unifiable (g_, vs_, vs'_) && Unify.unifiable (g_, us_, us'_)
          then sc ops
          else ops
        end
      | g_, O.Lex l_, O.Lex l'_, sc, ops -> ordeqs (g_, l_, l'_, sc, ops)
      | g_, O.Simul l_, O.Simul l'_, sc, ops -> ordeqs (g_, l_, l'_, sc, ops)

    and ordeqs = function
      | g_, [], [], sc, ops -> sc ops
      | g_, o_ :: l_, o'_ :: l'_, sc, ops ->
          ordeq
            ( g_,
              o_,
              o'_,
              (function ops' -> ordeqs (g_, l_, l'_, sc, ops')),
              ops )

    and ordle (g_, o_, o'_, sc, ops) =
      let ops' =
        Cs_manager.trail (function () -> ordeq (g_, o_, o'_, sc, ops))
      in
      ordlt (g_, o_, o'_, sc, ops')

    let rec createEVars = function
      | M.Prefix (I.Null, I.Null, I.Null) ->
          (M.Prefix (I.Null, I.Null, I.Null), I.id)
      | M.Prefix (I.Decl (g_, d_), I.Decl (m_, M.Top), I.Decl (b_, b)) ->
          let M.Prefix (g'_, m'_, b'_), s' =
            createEVars (M.Prefix (g_, m_, b_))
          in
          ( M.Prefix
              ( I.Decl (g'_, I.decSub (d_, s')),
                I.Decl (m'_, M.Top),
                I.Decl (b'_, b) ),
            I.dot1 s' )
      | M.Prefix (I.Decl (g_, I.Dec (_, v_)), I.Decl (m_, M.Bot), I.Decl (b_, _))
        ->
          let M.Prefix (g'_, m'_, b'_), s' =
            createEVars (M.Prefix (g_, m_, b_))
          in
          let x_ = I.newEVar (g'_, I.EClo (v_, s')) in
          (M.Prefix (g'_, m'_, b'_), I.Dot (I.Exp x_, s'))

    let rec select (g_, vs_) = selectW (g_, Whnf.whnf vs_)

    and selectW (g_, (I.Pi (((I.Dec (_, v1_) as d_), _), v2_), s)) =
      let rec select' (g_, (vs1_, vs2_)) = selectW' (g_, (vs1_, Whnf.whnf vs2_))
      and selectW' = function
        | g_, (vs1_, ((I.Root _, _) as vs2_)) -> (g_, (vs1_, vs2_))
        | g_, ((v1_, s1), (I.Pi ((d_, p_), v2'_), s2)) ->
            select'
              ( I.Decl (g_, I.decSub (d_, s2)),
                ((v1_, I.comp (s1, I.shift)), (v2'_, I.dot1 s2)) )
      in
      select'
        ( I.Decl (g_, I.decSub (d_, s)),
          ((v1_, I.comp (s, I.shift)), (v2_, I.dot1 s)) )

    let rec lemma (s_, t, ops) =
      let (M.State (name, gm_, v_)) = Lemma.apply (s_, t) in
      let M.Prefix (g'_, m'_, b'_), s' = createEVars gm_ in
      let g''_, ((I.Root (I.Const a1, s1_), s1), (I.Root (I.Const a2, s2_), s2))
          =
        select (g'_, (v_, s'))
      in
      ( g''_,
        vector (a1, (s1_, s1)),
        vector (a2, (s2_, s2)),
        (function
        | ops' ->
            MetaAbstract.abstract
              (M.State (name, M.Prefix (g'_, m'_, b'_), I.EClo (v_, s')))
            :: ops'),
        ops )

    let rec expandLazy' = function
      | s_, empty_, ops -> ops
      | s_, O.Le (t, l_), ops -> expandLazy' (s_, l_, ordle (lemma (s_, t, ops)))
      | s_, O.Lt (t, l_), ops -> expandLazy' (s_, l_, ordlt (lemma (s_, t, ops)))

    let rec recursionDepth v_ =
      let rec recursionDepth' = function
        | I.Root _, n -> n
        | I.Pi (_, v_), n -> recursionDepth' (v_, n + 1)
      in
      recursionDepth' (v_, 0)

    let rec expandLazy (M.State (_, _, v_) as s_) =
      begin if recursionDepth v_ > !MetaGlobal.maxRecurse then []
      else expandLazy' (s_, O.mutLookup (I.targetFam v_), [])
      end

    let rec inputConv (vs1_, vs2_) = inputConvW (Whnf.whnf vs1_, Whnf.whnf vs2_)

    and inputConvW
        ((I.Root (I.Const c1, s1_), s1), (I.Root (I.Const c2, s2_), s2)) =
      begin if c1 = c2 then
        inputConvSpine
          ( valOf (ModeTable.modeLookup c1),
            ((s1_, s1), (I.constType c1, I.id)),
            ((s2_, s2), (I.constType c2, I.id)) )
      else false
      end

    and inputConvSpine = function
      | Modes.Modesyn.ModeSyn.Mnil, ((s1_, _), _), ((s2_, _), _) -> true
      | mS, ((I.SClo (s1_, s1'), s1), vs1_), (ss2_, vs2_) ->
          inputConvSpine (mS, ((s1_, I.comp (s1', s1)), vs1_), (ss2_, vs2_))
      | mS, (ss1_, vs1_), ((I.SClo (s2_, s2'), s2), vs2_) ->
          inputConvSpine (mS, (ss1_, vs1_), ((s2_, I.comp (s2', s2)), vs2_))
      | ( Modes.Modesyn.ModeSyn.Mapp (Modes.Modesyn.ModeSyn.Marg (Modes.Modesyn.ModeSyn.Minus, _), mS),
          ((I.App (u1_, s1_), s1), (I.Pi ((I.Dec (_, v1_), _), w1_), t1)),
          ((I.App (u2_, s2_), s2), (I.Pi ((I.Dec (_, v2_), _), w2_), t2)) ) ->
          Conv.conv ((v1_, t1), (v2_, t2))
          && inputConvSpine
               ( mS,
                 ((s1_, s1), (w1_, I.Dot (I.Exp (I.EClo (u1_, s1)), t1))),
                 ((s2_, s2), (w2_, I.Dot (I.Exp (I.EClo (u1_, s1)), t2))) )
      | ( Modes.Modesyn.ModeSyn.Mapp (Modes.Modesyn.ModeSyn.Marg (Modes.Modesyn.ModeSyn.Plus, _), mS),
          ((I.App (u1_, s1_), s1), (I.Pi ((I.Dec (_, v1_), _), w1_), t1)),
          ((I.App (u2_, s2_), s2), (I.Pi ((I.Dec (_, v2_), _), w2_), t2)) ) ->
          inputConvSpine
            ( mS,
              ((s1_, s1), (w1_, I.Dot (I.Exp (I.EClo (u1_, s1)), t1))),
              ((s2_, s2), (w2_, I.Dot (I.Exp (I.EClo (u2_, s2)), t2))) )

    let rec removeDuplicates = function
      | [] -> []
      | s'_ :: ops ->
          let rec compExp (vs1_, vs2_) =
            compExpW (Whnf.whnf vs1_, Whnf.whnf vs2_)
          and compExpW = function
            | vs1_, (I.Root _, _) -> false
            | ((v1_, s1) as vs1_), (I.Pi ((d2_, _), v2_), s2) ->
                compDec (vs1_, (d2_, s2))
                || compExp ((v1_, I.comp (s1, I.shift)), (v2_, I.dot1 s2))
          and compDec (vs1_, (I.Dec (_, v2_), s2)) =
            inputConv (vs1_, (v2_, s2))
          in
          let rec check (M.State (name, gm_, v_)) =
            checkW (Whnf.whnf (v_, I.id))
          and checkW (I.Pi ((d_, _), v_), s) =
            checkDec ((d_, I.comp (s, I.shift)), (v_, I.dot1 s))
          and checkDec ((I.Dec (_, v1_), s1), vs2_) =
            compExp ((v1_, s1), vs2_)
          in
          begin if check s'_ then removeDuplicates ops
          else s'_ :: removeDuplicates ops
          end

    let rec fillOps = function
      | [] -> []
      | s'_ :: ops ->
          let rec fillOps' = function
            | [] -> []
            | o_ :: _ -> Filling.apply o_
          in
          let fillop, _ = Filling.expand s'_ in
          fillOps' fillop @ fillOps ops

    let rec expandEager s_ = removeDuplicates (fillOps (expandLazy s_))
    let rec apply s_ = s_

    let rec menu
        (M.State (name, M.Prefix (g'_, m'_, b'_), I.Pi ((I.Dec (_, v_), _), _))
         as s_) =
      "Recursion : " ^ Print.expToString (g'_, v_)

    let rec handleExceptions f p_ =
      try f p_ with Order.Error s -> raise (Error s)
  end

  (* Quantifier to mark parameters *)
  (* Q ::= Uni                     *)
  (*     | Ex                      *)
  (* If Q marks all parameters in a context G we write   G : Q               *)
  (* duplicate code? -fp *)
  (* vector (c, (S, s)) = P'

       Invariant:
       If   . |- c : V   G |- s : G'    G' |- S : V > type
       and  V = {x1:V1} ... {xn:Vn} type
       and  G |- S[s] = U1 .. Un : V[s] > type
       and  sel (c) = i1 .. im
       then P' = (U1'[s1']: V1'[t1'], .., U1'[sm']: V1'[tm'])
       and  G |- sj' : Gj'    Gj' |- Uj' : V1j'
       and  G |- tj' : Gj'    Gj' |- Vj' : L
       and  G |- Vj' [tj'] = V1j' [sj'] : L
       and  G |- Uik = Uk'[sk']
    *)
  (* select'W (1, _, (I.Root _, _)) cannot occur by invariant ! *)
  (* set_parameter (G, X, k, sc, ops) = ops'

       Invariant:
       appends a list of recursion operators to ops after
       instantiating X with all possible local parameters (between 1 and k)
    *)
  (* ltinit (G, k, ((U1, s1), (V2, s2)), ((U3, s3), (V4, s4)), sc, ops) = ops'

       Invariant:
       If   G = G0, Gp    (G0, global context, Gp, parameter context)
       and  |Gp| = k
       and  G |- s1 : G1   G1 |- U1 : V1
       and  G |- s2 : G2   G2 |- V2 : L
            G |- s3 : G1   G1 |- U3 : V3
       and  G |- s4 : G2   G2 |- V4 : L
       and  G |- V1[s1] == V2 [s2]
       and  G |- V3[s3] == V4 [s5]
       and  ops is a set of all all possible states
       and  sc is success continuation
       then ops' is an extension of ops, containing all
            recursion operators
    *)
  (* = I.decSub (D2, s2) *)
  (* lt (G, k, ((U, s1), (V, s2)), (U', s'), sc, ops) = ops'

       Invariant:
       If   G = G0, Gp    (G0, global context, Gp, parameter context)
       and  |Gp| = k
       and  G |- s1 : G1   G1 |- U1 : V1   (U1 [s1] in  whnf)
       and  G |- s2 : G2   G2 |- V2 : L    (V2 [s2] in  whnf)
            G |- s3 : G1   G1 |- U3 : V3
       and  G |- s4 : G2   G2 |- V4 : L
       and  k is the length of the local context
       and  G |- V1[s1] == V2 [s2]
       and  G |- V3[s3] == V4 [s5]
       and  ops is a set of already calculuate possible states
       and  sc is success continuation
       then ops' is an extension of ops, containing all
            recursion operators
    *)
  (* Vs is Root!!! *)
  (* (Us',Vs') may not be eta-expanded!!! *)
  (* n must be a local variable *)
  (* == I.targetFam V2' *)
  (* enforce that X gets only bound to parameters *)
  (* = I.newEVar (I.EClo (V2', s2')) *)
  (* = I.newEVar (I.EClo (V2', s2')) *)
  (* eq (G, ((U, s1), (V, s2)), (U', s'), sc, ops) = ops'

       Invariant:
       If   G |- s1 : G1   G1 |- U1 : V1   (U1 [s1] in  whnf)
       and  G |- s2 : G2   G2 |- V2 : L    (V2 [s2] in  whnf)
            G |- s3 : G1   G1 |- U3 : V3
       and  G |- s4 : G2   G2 |- V4 : L
       and  G |- V1[s1] == V2 [s2]
       and  G |- V3[s3] == V4 [s5]
       and  ops is a set of already calculuated possible states
       and  sc is success continuation
       then ops' is an extension of ops, containing all
            recursion operators resulting from U[s1] = U'[s']
    *)
  (* le (G, k, ((U, s1), (V, s2)), (U', s'), sc, ops) = ops'

       Invariant:
       If   G = G0, Gp    (G0, global context, Gp, parameter context)
       and  |Gp| = k
       and  G |- s1 : G1   G1 |- U1 : V1   (U1 [s1] in  whnf)
       and  G |- s2 : G2   G2 |- V2 : L    (V2 [s2] in  whnf)
            G |- s3 : G1   G1 |- U3 : V3
       and  G |- s4 : G2   G2 |- V4 : L
       and  k is the length of the local context
       and  G |- V1[s1] == V2 [s2]
       and  G |- V3[s3] == V4 [s5]
       and  ops is a set of already calculuated possible states
       and  sc is success continuation
       then ops' is an extension of ops, containing all
            recursion operators resulting from U[s1] <= U'[s']
    *)
  (* == I.targetFam V2' *)
  (* = I.newEVar (I.EClo (V2', s2')) *)
  (* enforces that X can only bound to parameter *)
  (* = I.newEVar (I.EClo (V2', s2')) *)
  (* ordlt (G, O1, O2, sc, ops) = ops'

       Invariant:
       If   G |- O1 augmented subterms
       and  G |- O2 augmented subterms
       and  ops is a set of already calculuated possible states
       and  sc is success continuation
       then ops' is an extension of ops, containing all
            recursion operators of all instantiations of EVars s.t. O1 is
            lexicographically smaller than O2
    *)
  (* ordltLex (G, L1, L2, sc, ops) = ops'

       Invariant:
       If   G |- L1 list of augmented subterms
       and  G |- L2 list of augmented subterms
       and  ops is a set of already calculuated possible states
       and  sc is success continuation
       then ops' is an extension of ops, containing all
            recursion operators of all instantiations of EVars s.t. L1 is
            lexicographically less then L2
    *)
  (* ordltSimul (G, L1, L2, sc, ops) = ops'

       Invariant:
       If   G |- L1 list of augmented subterms
       and  G |- L2 list of augmented subterms
       and  ops is a set of already calculuated possible states
       and  sc is success continuation
       then ops' is an extension of ops, containing all
            recursion operators of all instantiations of EVars s.t. L1 is
            simultaneously smaller than L2
    *)
  (* ordleSimul (G, L1, L2, sc, ops) = ops'

       Invariant:
       If   G |- L1 list of augmented subterms
       and  G |- L2 list of augmented subterms
       and  ops is a set of already calculuated possible states
       and  sc is success continuation
       then ops' is an extension of ops, containing all
            recursion operators of all instantiations of EVars s.t. L1 is
            simultaneously smaller than or equal to L2
    *)
  (* ordeq (G, O1, O2, sc, ops) = ops'

       Invariant:
       If   G |- O1 augmented subterms
       and  G |- O2 augmented subterms
       and  ops is a set of already calculuated possible states
       and  sc is success continuation
       then ops' is an extension of ops, containing all
            recursion operators of all instantiations of EVars s.t. O1 is
            convertible to O2
    *)
  (* ordlteqs (G, L1, L2, sc, ops) = ops'

       Invariant:
       If   G |- L1 list of augmented subterms
       and  G |- L2 list of augmented subterms
       and  ops is a set of already calculuated possible states
       and  sc is success continuation
       then ops' is an extension of ops, containing all
            recursion operators of all instantiations of EVars s.t. L1 is
            convertible to L2
    *)
  (* ordeq (G, O1, O2, sc, ops) = ops'

       Invariant:
       If   G |- O1 augmented subterms
       and  G |- O2 augmented subterms
       and  ops is a set of already calculuated possible states
       and  sc is success continuation
       then ops' is an extension of ops, containing all
1           recursion operators of all instantiations of EVars s.t. O1 is
            convertible to O2 or smaller than O2
    *)
  (* createEVars (G, M) = ((G', M'), s')

       Invariant:
       If   |- G ctx
       and  G |- M mtx
       then |- G' ctx
       and  G' |- M' mtx
       and  G' |- s' : G
    *)
  (* select (G, (V, s)) = (G', (V1', s1'), (V2', s2'))

     Invariant:
     If   G |- s : G1   G1 |- V : type
     and  G |- V [s] = {V1} ... {Vn} a S
     then G' = G, V1 .. Vn
     and  G' |- s1' : G1'   G1' |- V1' : type
     and  G' |- s2' : G2'   G2' |- V2' : type
     and  G' |- V1' [s1'] = V1 [^n]
     and  G' |- V2' [s2'] = a S
    *)
  (* lemma (S, t, ops) = (G', P', P'', abstract', ops')

       Invariant:
       If   S state  (S = ((G, M), V)
                     |- G ctx
                     G |- M mtx
                     G |- V = {V1} ... {Vn} a S)
       and  S' state derived from S by an inductive call to t
       and  ops a list of operators
       then G is context, where all - variables are replaced by EVars in S'
       and  P' is induction variable vector of EVars in the inductive call
       and  P'' is induction variable vector of the theorem S.
       and  G' |- P' : (V1' .. Vn')
              (where  t : {W1} ..{Wm} b S, and Vi' are among W1 .. Wm)
       and  G'' |- P'' : (V1'' .. Vn'')
              (where  a : {W1} ..{Wm} b S, and Vi'' are among W1 .. Wm)

    *)
  (* expandLazy' (S, L, ops) = ops'

       Invariant:
       If   S state
       and  L list of mutual recursive type families
       and  ops a list of operators
       then ops' extends ops by all operators
         representing inductive calls to theorems in L
    *)
  (* expandLazy S = ops'

       Invariant:
       If   S State
       then ops' a list of operations which cause a recursive call
         (only induction variables are instantiated)
    *)
  (* inputConv ((V1, s1), (V2, s2)) = B

       Invariant:
       If  G |- s1 : G1   G1 |- V1 : L
       and G |- s2 : G2   G2 |- V2 : L
       and G |- V1[s1] = c1 ; S1
       and G |- V2[s2] = c2 ; S2
       then B' holds iff c1 =  c2 and V1[s1] ==+ V2[s2]   (convertible on + arguments of c1)
    *)
  (* s1 = s2 = id *)
  (* S1 = S2 = Nil *)
  (* BUG: use the same variable (U1, s1) to continue comparing! --cs
                  in ((S2, s2), (W2, I.Dot (I.Exp (I.EClo (U2, s2), V2), t2))))
             FIXED: --cs Mon Nov  9 19:38:55 EST 1998 *)
  (* removeDuplicates ops = ops'

       Invariant:
       If   ops is a list of recursion operators,
       then ops' is a sublist of ops, s.t.
         forall S = ((G, M), V) in ops'
               |- G ctx
               G |- M mtx
               G |- V = {V0} .. {Vn} a ; S : type
               and Vi = ci ; S'
               and forall 1 <= i <= n:
                 either ci =/= c0 orelse
                 G, V0 .. Vi |- V0 [^ i] =/=+ Vi (not convertible on + arguments on c0)
    *)
  (* fillOps ops = ops'

       Invariant:
       If   ops is a list of lazy recursion operators
       then ops' is a list of recursion operators combined with a filling
         operator to fill non-index variables.
    *)
  (* expandEager S = ops'

       Invariant:
       If   S State
       then ops' a list of operations which cause a recursive call
         (all variables of recursive call are instantiated)
    *)
  let expandLazy = handleExceptions expandLazy
  let expandEager = handleExceptions expandEager
  let apply = apply
  let menu = menu
end
(*! structure Cs_manager : CS_MANAGER !*)
(*! sharing Cs_manager.IntSyn = MetaSyn'.IntSyn !*)
(* local *)
(* functor Recursion *)

(* # 1 "src/m2/recursion.sml.ml" *)
