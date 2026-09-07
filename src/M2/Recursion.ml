open! Global.Global_
open! Intsyn.Lambda_
open! Names.Names_
open! Modes
open! Formatter.Formatter_
open! Print.Print_
open! Solvers.Solvers_

(* # 1 "src/m2/Recursion.sig.ml" *)
open Metasyn

(* Recursion *)
(* Author: Carsten Schuermann *)
include RECURSION
(* signature RECURSION *)

(* # 1 "src/m2/Recursion.fun.ml" *)
open! Basis
open Metasyn
open MetaGlobal
open Modetable
open MetaPrint
open MetaAbstract

(* Recursion *)
(* Author: Carsten Schuermann *)
(* See [Rohwedder,Pfenning ESOP'96] *)

exception Error of string

let () =
  Printexc.register_printer (function Error msg -> Some msg | _ -> None)

module Recursion (Recursion__0 : sig
  module Global : GLOBAL
  module MetaGlobal : METAGLOBAL.METAGLOBAL
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
  module Lemma : LEMMA.LEMMA with module MetaSyn = MetaSyn'
  module Filling : FILLING.FILLING with module MetaSyn = MetaSyn'
  module MetaPrint : METAPRINT.METAPRINT with module MetaSyn = MetaSyn'
  module MetaAbstract : METAABSTRACT.METAABSTRACT with module MetaSyn = MetaSyn'
  module Formatter : FORMATTER
end) : RECURSION.RECURSION with module MetaSyn = Recursion__0.MetaSyn' = struct
  open Recursion__0
  module MetaSyn = MetaSyn'

  exception Error = Error

  type nonrec operator = MetaSyn.state

  open! struct
    module M = MetaSyn
    module I = IntSyn
    module O = Order
    module N = Names
    module F = Formatter

    type quantifier = Universal | Existential

    let vectorToString (g, o) =
      let rec fmtOrder = function
        | Order.Arg (us, vs) ->
            [
              F.string (Print.expToString g (I.EClo (fst us, snd us)));
              F.string ":";
              F.string (Print.expToString g (I.EClo (fst vs, snd vs)));
            ]
        | Order.Lex l -> [ F.string "{"; F.hVbox (fmtOrders l); F.string "}" ]
        | Order.Simul l ->
            [ F.string "["; F.hVbox (fmtOrders l); F.string "]" ]
      and fmtOrders = function
        | [] -> []
        | o :: [] -> fmtOrder o
        | o :: l -> fmtOrder o @ (F.string " " :: fmtOrders l)
      in
      F.makestring_fmt (F.hVbox (fmtOrder o))

    let vector (c, (s_, s)) =
      let vid = (I.constType c, I.id) in
      let rec select' (n, (ss', vs'')) = select'W (n, (ss', Whnf.whnf vs''))
      and select'W = function
        | 1, ((I.App (u', s'_), s'), (I.Pi ((I.Dec (_, v''), _), _), s'')) ->
            ((u', s'), (v'', s''))
        | n, ((I.SClo (s', s1'), s2'), vs'') ->
            select'W (n, ((s', I.comp s1' s2'), vs''))
        | n, ((I.App (u', s'_), s'), (I.Pi ((I.Dec (_, v1''), _), v2''), s''))
          ->
            select'
              (n - 1, ((s'_, s'), (v2'', I.Dot (I.Exp (I.EClo (u', s')), s''))))
      in
      let rec select = function
        | O.Arg n -> O.Arg (select' (n, ((s_, s), vid)))
        | O.Lex l -> O.Lex (map select l)
        | O.Simul l -> O.Simul (map select l)
      in
      select (O.selLookup c)

    let set_parameter (g, (I.EVar (r, _, v, _) as x), k, sc, ops) =
      let rec set_parameter' (k', ops') = match k' with
        | 0 -> ops'
        | k' ->
            let (I.Dec (_, v') as d') = I.ctxDec g k' in
            let ops'' =
              CsManager.trail (function () ->
                  begin if
                    Unify.unifiable g (v, I.id) (v', I.id)
                    && Unify.unifiable
                         g (x, I.id) (I.Root (I.BVar k', I.Nil), I.id)
                  then sc ops'
                  else ops'
                  end)
            in
            set_parameter' (k' - 1, ops'')
      in
      set_parameter' (k, ops)

    let rec ltinit (g, k, (us, vs), usVs', sc, ops) =
      ltinitW (g, k, Whnf.whnfEta us vs, usVs', sc, ops)

    and ltinitW (g, k, a, usVs', sc, ops) = match a, usVs' with
      | (us, ((I.Root _, _) as vs)), usVs' ->
          lt (g, k, (us, vs), usVs', sc, ops)
      | ((I.Lam (d1, u), s1), (I.Pi (d2, v), s2)), ((u', s1'), (v', s2')) ->
          ltinit
            ( I.Decl (g, I.decSub d1 s1),
              k + 1,
              ((u, I.dot1 s1), (v, I.dot1 s2)),
              ((u', I.comp s1' I.shift), (v', I.comp s2' I.shift)),
              sc,
              ops )

    and lt (g, k, (us, vs), (us', vs'), sc, ops) =
      ltW (g, k, (us, vs), Whnf.whnfEta us' vs', sc, ops)

    and ltW (g, k, a, b, sc, ops) = match a, b with
      | (us, vs), ((I.Root (I.Const c, s'_), s'), vs') ->
          ltSpine
            (g, k, (us, vs), ((s'_, s'), (I.constType c, I.id)), sc, ops)
      | (us, vs), ((I.Root (I.BVar n, s'_), s'), vs') ->
          begin if n <= k then
            let (I.Dec (_, v')) = I.ctxDec g n in
            ltSpine (g, k, (us, vs), ((s'_, s'), (v', I.id)), sc, ops)
          else ops
          end
      | _, ((I.EVar _, _), _) -> ops
      | ((u, s1), (v, s2)), ( (I.Lam ((I.Dec (_, v1') as d), u'), s1'),
            (I.Pi ((I.Dec (_, v2'), _), v'), s2') ) ->
          begin if Subordinate.equiv (I.targetFam v) (I.targetFam v1') then
            let x = I.newEVar g (I.EClo (v1', s1')) in
            let sc' ops' = set_parameter (g, x, k, sc, ops') in
            lt
              ( g,
                k,
                ((u, s1), (v, s2)),
                ((u', I.Dot (I.Exp x, s1')), (v', I.Dot (I.Exp x, s2'))),
                sc',
                ops )
          else
            begin if Subordinate.below (I.targetFam v1') (I.targetFam v) then
              let x = I.newEVar g (I.EClo (v1', s1')) in
              lt
                ( g,
                  k,
                  ((u, s1), (v, s2)),
                  ((u', I.Dot (I.Exp x, s1')), (v', I.Dot (I.Exp x, s2'))),
                  sc,
                  ops )
            else ops
            end
          end

    and ltSpine (g, k, (us, vs), (ss', vs'), sc, ops) =
      ltSpineW (g, k, (us, vs), (ss', Whnf.whnf vs'), sc, ops)

    and ltSpineW (g, k, a, b, sc, ops) = match a, b with
      | (us, vs), ((I.Nil, _), _) -> ops
      | (us, vs), ((I.SClo (s, s'), s''), vs') ->
          ltSpineW (g, k, (us, vs), ((s, I.comp s' s''), vs'), sc, ops)
      | (us, vs), ((I.App (u', s'), s1'), (I.Pi ((I.Dec (_, v1'), _), v2'), s2')) ->
          let ops' =
            le (g, k, (us, vs), ((u', s1'), (v1', s2')), sc, ops)
          in
          ltSpine
            ( g,
              k,
              (us, vs),
              ((s', s1'), (v2', I.Dot (I.Exp (I.EClo (u', s1')), s2'))),
              sc,
              ops' )

    and eq (g, (us, vs), (us', vs'), sc, ops) =
      CsManager.trail (function () ->
          begin if
            Unify.unifiable g vs vs' && Unify.unifiable g us us'
          then sc ops
          else ops
          end)

    and le (g, k, (us, vs), (us', vs'), sc, ops) =
      let ops' = eq (g, (us, vs), (us', vs'), sc, ops) in
      leW (g, k, (us, vs), Whnf.whnfEta us' vs', sc, ops')

    and leW (g, k, a, b, sc, ops) = match a, b with
      | ((u, s1), (v, s2)), ( (I.Lam ((I.Dec (_, v1') as d), u'), s1'),
            (I.Pi ((I.Dec (_, v2'), _), v'), s2') ) ->
          begin if Subordinate.equiv (I.targetFam v) (I.targetFam v1') then
            let x = I.newEVar g (I.EClo (v1', s1')) in
            let sc' ops' = set_parameter (g, x, k, sc, ops') in
            le
              ( g,
                k,
                ((u, s1), (v, s2)),
                ((u', I.Dot (I.Exp x, s1')), (v', I.Dot (I.Exp x, s2'))),
                sc',
                ops )
          else
            begin if Subordinate.below (I.targetFam v1') (I.targetFam v) then
              let x = I.newEVar g (I.EClo (v1', s1')) in
              le
                ( g,
                  k,
                  ((u, s1), (v, s2)),
                  ((u', I.Dot (I.Exp x, s1')), (v', I.Dot (I.Exp x, s2'))),
                  sc,
                  ops )
            else ops
            end
          end
      | (us, vs), (us', vs') ->
          lt (g, k, (us, vs), (us', vs'), sc, ops)

    let rec ordlt (g, a, b, sc, ops) = match a, b with
      | O.Arg usVs, O.Arg usVs' ->
          ltinit (g, 0, usVs, usVs', sc, ops)
      | O.Lex l, O.Lex l' -> ordltLex (g, l, l', sc, ops)
      | O.Simul l, O.Simul l' -> ordltSimul (g, l, l', sc, ops)

    and ordltLex (g, a, b, sc, ops) = match a, b with
      | [], [] -> ops
      | o :: l, o' :: l' ->
          let ops' =
            CsManager.trail (function () -> ordlt (g, o, o', sc, ops))
          in
          ordeq
            ( g,
              o,
              o',
              (function ops'' -> ordltLex (g, l, l', sc, ops'')),
              ops' )

    and ordltSimul (g, a, b, sc, ops) = match a, b with
      | [], [] -> ops
      | o :: l, o' :: l' ->
          let ops'' =
            CsManager.trail (function () ->
                ordlt
                  ( g,
                    o,
                    o',
                    (function ops' -> ordleSimul (g, l, l', sc, ops')),
                    ops ))
          in
          ordeq
            ( g,
              o,
              o',
              (function ops' -> ordltSimul (g, l, l', sc, ops')),
              ops'' )

    and ordleSimul (g, a, b, sc, ops) = match a, b with
      | [], [] -> sc ops
      | o :: l, o' :: l' ->
          ordle
            ( g,
              o,
              o',
              (function ops' -> ordleSimul (g, l, l', sc, ops')),
              ops )

    and ordeq (g, a, b, sc, ops) = match a, b with
      | O.Arg (us, vs), O.Arg (us', vs') ->
          begin if
            Unify.unifiable g vs vs' && Unify.unifiable g us us'
          then sc ops
          else ops
          end
      | O.Lex l, O.Lex l' -> ordeqs (g, l, l', sc, ops)
      | O.Simul l, O.Simul l' -> ordeqs (g, l, l', sc, ops)

    and ordeqs (g, a, b, sc, ops) = match a, b with
      | [], [] -> sc ops
      | o :: l, o' :: l' ->
          ordeq
            ( g,
              o,
              o',
              (function ops' -> ordeqs (g, l, l', sc, ops')),
              ops )

    and ordle (g, o, o', sc, ops) =
      let ops' =
        CsManager.trail (function () -> ordeq (g, o, o', sc, ops))
      in
      ordlt (g, o, o', sc, ops')

    let rec createEVars = function
      | M.Prefix (I.Null, I.Null, I.Null) ->
          (M.Prefix (I.Null, I.Null, I.Null), I.id)
      | M.Prefix (I.Decl (g, d), I.Decl (m, M.Top), I.Decl (b_, b)) ->
          let M.Prefix (g', m', b'), s' =
            createEVars (M.Prefix (g, m, b_))
          in
          ( M.Prefix
              ( I.Decl (g', I.decSub d s'),
                I.Decl (m', M.Top),
                I.Decl (b', b) ),
            I.dot1 s' )
      | M.Prefix (I.Decl (g, I.Dec (_, v)), I.Decl (m, M.Bot), I.Decl (b, _))
        ->
          let M.Prefix (g', m', b'), s' =
            createEVars (M.Prefix (g, m, b))
          in
          let x = I.newEVar g' (I.EClo (v, s')) in
          (M.Prefix (g', m', b'), I.Dot (I.Exp x, s'))

    let rec select (g, vs) = selectW (g, Whnf.whnf vs)

    and selectW (g, (I.Pi (((I.Dec (_, v1) as d), _), v2), s)) =
      let rec select' (g, (vs1, vs2)) = selectW' (g, (vs1, Whnf.whnf vs2))
      and selectW' (g, a) = match a with
        | (vs1, ((I.Root _, _) as vs2)) -> (g, (vs1, vs2))
        | ((v1, s1), (I.Pi ((d, p), v2'), s2)) ->
            select'
              ( I.Decl (g, I.decSub d s2),
                ((v1, I.comp s1 I.shift), (v2', I.dot1 s2)) )
      in
      select'
        ( I.Decl (g, I.decSub d s),
          ((v1, I.comp s I.shift), (v2, I.dot1 s)) )

    let lemma (s, t, ops) =
      let (M.State (name, gm, v)) = Lemma.apply s t in
      let M.Prefix (g', m', b'), s' = createEVars gm in
      let g'', ((I.Root (I.Const a1, s1_), s1), (I.Root (I.Const a2, s2_), s2))
          =
        select (g', (v, s'))
      in
      ( g'',
        vector (a1, (s1_, s1)),
        vector (a2, (s2_, s2)),
        (function
        | ops' ->
            MetaAbstract.abstract
              (M.State (name, M.Prefix (g', m', b'), I.EClo (v, s')))
            :: ops'),
        ops )

    let rec expandLazy' (s, empty, ops) = match empty with
      | empty -> ops
      | O.Le (t, l) -> expandLazy' (s, l, ordle (lemma (s, t, ops)))
      | O.Lt (t, l) -> expandLazy' (s, l, ordlt (lemma (s, t, ops)))

    let recursionDepth v =
      let rec recursionDepth' (a, n) = match a with
        | I.Root _ -> n
        | I.Pi (_, v) -> recursionDepth' (v, n + 1)
      in
      recursionDepth' (v, 0)

    let expandLazy (M.State (_, _, v) as s) =
      begin if recursionDepth v > !MetaGlobal.maxRecurse then []
      else expandLazy' (s, O.mutLookup (I.targetFam v), [])
      end

    let rec inputConv (vs1, vs2) = inputConvW (Whnf.whnf vs1, Whnf.whnf vs2)

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
      | Modes.Modesyn.ModeSyn.Mnil, ((s1, _), _), ((s2, _), _) -> true
      | mS, ((I.SClo (s1_, s1'), s1), vs1), (ss2, vs2) ->
          inputConvSpine (mS, ((s1_, I.comp s1' s1), vs1), (ss2, vs2))
      | mS, (ss1, vs1), ((I.SClo (s2_, s2'), s2), vs2) ->
          inputConvSpine (mS, (ss1, vs1), ((s2_, I.comp s2' s2), vs2))
      | ( Modes.Modesyn.ModeSyn.Mapp
            (Modes.Modesyn.ModeSyn.Marg (Modes.Modesyn.ModeSyn.Minus, _), mS),
          ((I.App (u1, s1_), s1), (I.Pi ((I.Dec (_, v1), _), w1), t1)),
          ((I.App (u2, s2_), s2), (I.Pi ((I.Dec (_, v2), _), w2), t2)) ) ->
          Conv.conv (v1, t1) (v2, t2)
          && inputConvSpine
               ( mS,
                 ((s1_, s1), (w1, I.Dot (I.Exp (I.EClo (u1, s1)), t1))),
                 ((s2_, s2), (w2, I.Dot (I.Exp (I.EClo (u1, s1)), t2))) )
      | ( Modes.Modesyn.ModeSyn.Mapp
            (Modes.Modesyn.ModeSyn.Marg (Modes.Modesyn.ModeSyn.Plus, _), mS),
          ((I.App (u1, s1_), s1), (I.Pi ((I.Dec (_, v1), _), w1), t1)),
          ((I.App (u2, s2_), s2), (I.Pi ((I.Dec (_, v2), _), w2), t2)) ) ->
          inputConvSpine
            ( mS,
              ((s1_, s1), (w1, I.Dot (I.Exp (I.EClo (u1, s1)), t1))),
              ((s2_, s2), (w2, I.Dot (I.Exp (I.EClo (u2, s2)), t2))) )

    let rec removeDuplicates = function
      | [] -> []
      | s' :: ops ->
          let rec compExp (vs1, vs2) = compExpW (Whnf.whnf vs1, Whnf.whnf vs2)
          and compExpW = function
            | vs1, (I.Root _, _) -> false
            | ((v1, s1) as vs1), (I.Pi ((d2, _), v2), s2) ->
                compDec (vs1, (d2, s2))
                || compExp ((v1, I.comp s1 I.shift), (v2, I.dot1 s2))
          and compDec (vs1, (I.Dec (_, v2), s2)) =
            inputConv (vs1, (v2, s2))
          in
          let rec check (M.State (name, gm, v)) = checkW (Whnf.whnf (v, I.id))
          and checkW (I.Pi ((d, _), v), s) =
            checkDec (d, I.comp s I.shift) (v, I.dot1 s)
          and checkDec (I.Dec (_, v1), s1) vs2 = compExp ((v1, s1), vs2) in
          begin if check s' then removeDuplicates ops
          else s' :: removeDuplicates ops
          end

    let rec fillOps = function
      | [] -> []
      | s' :: ops ->
          let fillOps' = function [] -> [] | o :: _ -> Filling.apply o in
          let fillop, _ = Filling.expand s' in
          fillOps' fillop @ fillOps ops

    let expandEager s = removeDuplicates (fillOps (expandLazy s))
    let apply s = s

    let menu
        (M.State (name, M.Prefix (g', m', b'), I.Pi ((I.Dec (_, v), _), _))
         as s) =
      "Recursion : " ^ Print.expToString g' v

    let handleExceptions f p = try f p with Order.Error s -> raise (Error s)
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
(*! structure CsManager : CS_MANAGER !*)
(*! sharing CsManager.IntSyn = MetaSyn'.IntSyn !*)
(* local *)
(* functor Recursion *)

(* # 1 "src/m2/Recursion.sml.ml" *)
