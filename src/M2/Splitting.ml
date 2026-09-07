open! Global.Global_
open! Intsyn.Lambda_
open! Modes
open! Print.Print_
open! Index.Index_
open! Solvers.Solvers_

(* # 1 "src/m2/Splitting.sig.ml" *)
open Metasyn

(* Splitting *)
(* Author: Carsten Schuermann *)
include SPLITTING
(* signature SPLITTING *)

(* # 1 "src/m2/Splitting.fun.ml" *)
open! Basis
open Metasyn
open MetaAbstract
open MetaPrint
open Modetable

(* Splitting *)
(* Author: Carsten Schuermann *)

exception Error of string

let () =
  Printexc.register_printer (function Error msg -> Some msg | _ -> None)

module Splitting (Splitting__0 : sig
  module Global : GLOBAL
  module MetaSyn' : Metasyn.METASYN
  module MetaAbstract : METAABSTRACT.METAABSTRACT with module MetaSyn = MetaSyn'
  module MetaPrint : METAPRINT.METAPRINT with module MetaSyn = MetaSyn'
  module ModeTable : Modetable.MODETABLE

  (*! sharing Modes.Modesyn.ModeSyn.IntSyn = MetaSyn'.IntSyn !*)
  module Whnf : WHNF

  (*! sharing Whnf.IntSyn = MetaSyn'.IntSyn !*)
  module Index : INDEX

  (*! sharing Index.IntSyn = MetaSyn'.IntSyn !*)
  module Print : PRINT

  (*! sharing Print.IntSyn = MetaSyn'.IntSyn !*)
  module Unify : UNIFY
end) : SPLITTING.SPLITTING with module MetaSyn = Splitting__0.MetaSyn' = struct
  open Splitting__0
  module MetaSyn = MetaAbstract.MetaSyn

  exception Error = Error

  (* Invariant:
     Case analysis generates a list of successor states
     (the cases) from a given State.

     'a flag marks cases where unification of the types
     succeeded as ""Active"", and cases where there were
     leftover constraints after unification as ""Inactive"".

     NB: cases where unification fails are not considered

     Consequence: Only those splitting operators can be
     applied which do not generate inactive cases.
  *)
  type 'a flag = Active of 'a | InActive [@@deriving eq, ord, show]
  type nonrec operator = (MetaSyn.state * int) * MetaSyn.state flag list

  open! struct
    module M = MetaSyn
    module I = IntSyn

    let rec constCases (g, vs, a, abstract, ops) = match a with
      | [] -> ops
      | (I.Const c as h) :: sgn ->
          let u, vs' = M.createAtomConst g h in
          constCases
            ( g,
              vs,
              sgn,
              abstract,
              CsManager.trail (function () ->
                  (try
                     begin if Unify.unifiable g vs vs' then
                       Active
                         (abstract (I.conDecName (I.sgnLookup c) ^ "/", u))
                       :: ops
                     else ops
                     end
                   with MetaAbstract.Error _ -> InActive :: ops)) )
      | (I.Def c as h) :: sgn ->
          let u, vs' = M.createAtomConst g h in
          constCases
            ( g,
              vs,
              sgn,
              abstract,
              CsManager.trail (function () ->
                  (try
                     begin if Unify.unifiable g vs vs' then
                       Active
                         (abstract (I.conDecName (I.sgnLookup c) ^ "/", u))
                       :: ops
                     else ops
                     end
                   with MetaAbstract.Error _ -> InActive :: ops)) )
      | _ :: sgn ->
          (* Skip other head types *)
          constCases (g, vs, sgn, abstract, ops)

    let rec paramCases (g, vs, k, abstract, ops) = match k with
      | 0 -> ops
      | k ->
          let u, vs' = M.createAtomBVar g k in
          paramCases
            ( g,
              vs,
              k - 1,
              abstract,
              CsManager.trail (function () ->
                  (try
                     begin if Unify.unifiable g vs vs' then
                       Active (abstract (Int.toString k ^ "/", u)) :: ops
                     else ops
                     end
                   with MetaAbstract.Error _ -> InActive :: ops)) )

    let rec lowerSplitDest (g, a, abstract) = match a with
      | ((I.Root (I.Const c, _) as v), s') ->
          constCases
            ( g,
              (v, s'),
              Index.lookup c,
              abstract,
              paramCases (g, (v, s'), I.ctxLength g, abstract, []) )
      | (I.Pi ((d, p), v), s') ->
          let d' = I.decSub d s' in
          lowerSplitDest
            ( I.Decl (g, d'),
              (v, I.dot1 s'),
              function name, u -> abstract (name, I.Lam (d', u)) )

    let split (M.Prefix (g, m, b), ((I.Dec (_, v) as d), s), abstract) =
      lowerSplitDest
        ( I.Null,
          (v, s),
          function
          | name', u' ->
              abstract (name', M.Prefix (g, m, b), I.Dot (I.Exp u', s)) )

    let rec occursInExp (k, a) = match a with
      | I.Uni _ -> false
      | I.Pi (dp, v) -> occursInDecP (k, dp) || occursInExp (k + 1, v)
      | I.Root (c, s) -> occursInCon (k, c) || occursInSpine (k, s)
      | I.Lam (d, v) -> occursInDec (k, d) || occursInExp (k + 1, v)
      | I.FgnExp (csid, fge) ->
          I.FgnExpStd.fold csid fge
            (function
              | u, b -> b || occursInExp (k, Whnf.normalize (u, I.id)))
            false

    and occursInCon (k, a) = match a with
      | I.BVar k' -> k = k'
      | I.Const _ -> false
      | I.Def _ -> false
      | I.Skonst _ -> false

    and occursInSpine (k, a) = match a with
      | I.Nil -> false
      | I.App (u, s) -> occursInExp (k, u) || occursInSpine (k, s)

    and occursInDec (k, I.Dec (_, v)) = occursInExp (k, v)
    and occursInDecP (k, (d, _)) = occursInDec (k, d)

    let isIndexInit k = false
    let isIndexSucc (d, isIndex) k = occursInDec (k, d) || isIndex (k + 1)
    let isIndexFail (d, isIndex) k = isIndex (k + 1)

    let rec checkVar = function
      | I.Decl (m, M.Top), 1 -> true
      | I.Decl (m, M.Bot), 1 -> false
      | I.Decl (m, _), k -> checkVar (m, k - 1)

    let rec checkExp (m, a) = match a with
      | I.Uni _ -> true
      | I.Pi ((d, p), v) ->
          checkDec m d && checkExp (I.Decl (m, M.Top), v)
      | I.Lam (d, v) ->
          checkDec m d && checkExp (I.Decl (m, M.Top), v)
      | I.Root (I.BVar k, s) -> checkVar (m, k) && checkSpine (m, s)
      | I.Root (_, s) -> checkSpine (m, s)

    and checkSpine (m, a) = match a with
      | I.Nil -> true
      | I.App (u, s) -> checkExp (m, u) && checkSpine (m, s)

    and checkDec m (I.Dec (_, v)) = checkExp (m, v)

    let modeEq = function
      | Modes.Modesyn.ModeSyn.Marg (Modes.Modesyn.ModeSyn.Plus, _), M.Top ->
          true
      | Modes.Modesyn.ModeSyn.Marg (Modes.Modesyn.ModeSyn.Minus, _), M.Bot ->
          true
      | _ -> false

    let rec inheritBelow (b', k', a, bdd') = match a, bdd' with
      | I.Lam (d', u'), bdd' ->
          inheritBelow (b', k' + 1, u', inheritBelowDec (b', k', d', bdd'))
      | I.Pi ((d', _), v'), bdd' ->
          inheritBelow (b', k' + 1, v', inheritBelowDec (b', k', d', bdd'))
      | I.Root (I.BVar n', s'), (b'_, d, d') ->
          begin if n' = k' + d' && n' > k' then
            inheritBelowSpine (b', k', s', (I.Decl (b'_, b'), d, d' - 1))
          else inheritBelowSpine (b', k', s', (b'_, d, d'))
          end
      | I.Root (c, s'), bdd' -> inheritBelowSpine (b', k', s', bdd')

    and inheritBelowSpine (b', k', a, bdd') = match a with
      | I.Nil -> bdd'
      | I.App (u', s') ->
          inheritBelowSpine (b', k', s', inheritBelow (b', k', u', bdd'))

    and inheritBelowDec (b', k', I.Dec (x, v'), bdd') =
      inheritBelow (b', k', v', bdd')

    let rec skip (k, a, bdd') = match a, bdd' with
      | I.Lam (d, u), bdd' -> skip (k + 1, u, skipDec (k, d, bdd'))
      | I.Pi ((d, _), v), bdd' -> skip (k + 1, v, skipDec (k, d, bdd'))
      | I.Root (I.BVar n, s), (b', d, d') ->
          begin if n = k + d && n > k then skipSpine (k, s, (b', d - 1, d'))
          else skipSpine (k, s, (b', d, d'))
          end
      | I.Root (c, s), bdd' -> skipSpine (k, s, bdd')

    and skipSpine (k, a, bdd') = match a with
      | I.Nil -> bdd'
      | I.App (u, s) -> skipSpine (k, s, skip (k, u, bdd'))

    and skipDec (k, I.Dec (x, v), bdd') = skip (k, v, bdd')

    let rec inheritExp (b_, k, a, k', b, bdd') = match a, b, bdd' with
      | I.Lam (d, u), I.Lam (d', u'), bdd' ->
          inheritExp
            (b_, k + 1, u, k' + 1, u', inheritDec (b_, k, d, k', d', bdd'))
      | I.Pi ((d, _), v), I.Pi ((d', _), v'), bdd' ->
          inheritExp
            (b_, k + 1, v, k' + 1, v', inheritDec (b_, k, d, k', d', bdd'))
      | (I.Root (I.BVar n, s) as v), v', (b', d, d') ->
          begin if n = k + d && n > k then
            skipSpine
              ( k,
                s,
                inheritNewRoot
                  (b_, I.ctxLookup b_ (n - k), k, v, k', v', (b', d, d')) )
          else
            begin if n > k + d then
              skipSpine
                ( k,
                  s,
                  inheritBelow
                    (I.ctxLookup b_ (n - k) - 1, k', v', (b', d, d')) )
            else
              let (I.Root (c', s')) = v' in
              inheritSpine (b_, k, s, k', s', (b', d, d'))
            end
          end
      | I.Root (c, s), I.Root (c', s'), bdd' ->
          inheritSpine (b_, k, s, k', s', bdd')

    and inheritNewRoot (b_, b, k, v, k', a, c) = match v, a, c with
      | I.Root (I.BVar n, s), (I.Root (I.BVar n', s') as v'), (b', d, d') ->
          begin if n' = k' + d' && n' > k' then
            inheritBelow (b, k', v', (b', d - 1, d'))
          else inheritBelow (b - 1, k', v', (b', d - 1, d'))
          end
      | v, v', (b', d, d') ->
          inheritBelow (b - 1, k', v', (b', d - 1, d'))

    and inheritSpine (b_, k, a, k', b, bdd') = match a, b with
      | I.Nil, I.Nil -> bdd'
      | I.App (u, s), I.App (u', s') ->
          inheritSpine
            (b_, k, s, k', s', inheritExp (b_, k, u, k', u', bdd'))

    and inheritDec (b, k, I.Dec (_, v), k', I.Dec (_, v'), bdd') =
      inheritExp (b, k, v, k', v', bdd')

    let rec inheritDTop (b_, k, a, k', b, bdd') = match a, b with
      | I.Pi ((I.Dec (_, v1), I.No), v2), I.Pi ((I.Dec (_, v1'), I.No), v2') ->
          inheritG
            ( b_,
              k,
              v1,
              k',
              v1',
              inheritDTop (b_, k + 1, v2, k' + 1, v2', bdd') )
      | (I.Root (I.Const cid, s) as v), (I.Root (I.Const cid', s') as v') ->
          let mS = valOf (ModeTable.modeLookup cid) in
          inheritSpineMode (M.Top, mS, b_, k, s, k', s', bdd')

    and inheritDBot (b_, k, a, k', b, bdd') = match a, b with
      | I.Pi ((I.Dec (_, v1), I.No), v2), I.Pi ((I.Dec (_, v1'), I.No), v2') ->
          inheritDBot (b_, k + 1, v2, k' + 1, v2', bdd')
      | I.Root (I.Const cid, s), I.Root (I.Const cid', s') ->
          let mS = valOf (ModeTable.modeLookup cid) in
          inheritSpineMode (M.Bot, mS, b_, k, s, k', s', bdd')

    and inheritG
        ( b,
          k,
          I.Root (I.Const cid, s),
          k',
          (I.Root (I.Const cid', s') as v'),
          bdd' ) =
      let mS = valOf (ModeTable.modeLookup cid) in
      inheritSpineMode
        ( M.Bot,
          mS,
          b,
          k,
          s,
          k',
          s',
          inheritSpineMode (M.Top, mS, b, k, s, k', s', bdd') )

    and inheritSpineMode (mode, a, b_, k, b, k', c, bdd') = match a, b, c with
      | Modes.Modesyn.ModeSyn.Mnil, I.Nil, I.Nil -> bdd'
      | Modes.Modesyn.ModeSyn.Mapp (m, mS), I.App (u, s), I.App (u', s') ->
          begin if modeEq (m, mode) then
            inheritSpineMode
              ( mode,
                mS,
                b_,
                k,
                s,
                k',
                s',
                inheritExp (b_, k, u, k', u', bdd') )
          else inheritSpineMode (mode, mS, b_, k, s, k', s', bdd')
          end

    let inheritSplitDepth
        ( (M.State (_, M.Prefix (g, m, b), v) as s),
          (M.State (name', M.Prefix (g', m', b'), v') as s') ) =
      let d = I.ctxLength g in
      let d' = I.ctxLength g' in
      let v = Whnf.normalize (v, I.id) in
      let v' = Whnf.normalize (v', I.id) in
      let b'', 0, 0 =
        inheritDBot
          (b, 0, v, 0, v', inheritDTop (b, 0, v, 0, v', (I.Null, d, d')))
      in
      M.State (name', M.Prefix (g', m', b''), v')

    let abstractInit (M.State (name, gm, v))
        (name', M.Prefix (g', m', b'), s') =
      inheritSplitDepth
        ( M.State (name, gm, v),
          MetaAbstract.abstract
            (M.State (name ^ name', M.Prefix (g', m', b'), I.EClo (v, s')))
        )

    let abstractCont ((d, mode, b), abstract)
        (name', M.Prefix (g', m', b'), s') =
      abstract
        ( name',
          M.Prefix
            ( I.Decl (g', I.decSub d s'),
              I.Decl (m', mode),
              I.Decl (b', b) ),
          I.dot1 s' )

    let makeAddressInit s k = (s, k)
    let makeAddressCont makeAddress k = makeAddress (k + 1)

    let rec expand' (a, isIndex, abstract, makeAddress) = match a with
      | M.Prefix (I.Null, I.Null, I.Null) ->
          (M.Prefix (I.Null, I.Null, I.Null), I.id, [])
      | M.Prefix
            (I.Decl (g, d), I.Decl (m, (M.Top as mode)), I.Decl (b_, b)) ->
          let M.Prefix (g', m', b'), s', ops =
            expand'
              ( M.Prefix (g, m, b_),
                isIndexSucc (d, isIndex),
                abstractCont ((d, mode, b), abstract),
                makeAddressCont makeAddress )
          in
          let (I.Dec (xOpt, v)) = d in
          let x = I.newEVar g' (I.EClo (v, s')) in
          let ops' =
            begin if b > 0 && (not (isIndex 1)) && checkDec m d then
              ( makeAddress 1,
                split (M.Prefix (g', m', b'), (d, s'), abstract) )
              :: ops
            else ops
            end
          in
          (M.Prefix (g', m', b'), I.Dot (I.Exp x, s'), ops')
      | M.Prefix
            (I.Decl (g, d), I.Decl (m, (M.Bot as mode)), I.Decl (b_, b)) ->
          let M.Prefix (g', m', b'), s', ops =
            expand'
              ( M.Prefix (g, m, b_),
                isIndexSucc (d, isIndex),
                abstractCont ((d, mode, b), abstract),
                makeAddressCont makeAddress )
          in
          ( M.Prefix
              ( I.Decl (g', I.decSub d s'),
                I.Decl (m', M.Bot),
                I.Decl (b', b) ),
            I.dot1 s',
            ops )

    let expand (M.State (name, M.Prefix (g, m, b), v) as s) =
      let _, _, ops =
        expand'
          ( M.Prefix (g, m, b),
            isIndexInit,
            abstractInit s,
            makeAddressInit s )
      in
      ops

    let index (_, sl) = List.length sl

    let apply (_, sl) =
      map
        (function
          | Active s -> s
          | InActive -> raise (Error "Not applicable: leftover constraints"))
        sl

    let menu (((M.State (name, M.Prefix (g, m_, b), v), i), sl) as op) =
      let rec active (a, n) = match a with
        | [] -> n
        | InActive :: l -> active (l, n)
        | Active _ :: l -> active (l, n + 1)
      in
      let rec inactive (a, n) = match a with
        | [] -> n
        | InActive :: l -> inactive (l, n + 1)
        | Active _ :: l -> inactive (l, n)
      in
      let indexToString = function
        | 0 -> "zero cases"
        | 1 -> "1 case"
        | n -> Int.toString n ^ " cases"
      in
      let flagToString (n, m) = match m with
        | 0 -> ""
        | m ->
            (((" [active: " ^ Int.toString n) ^ " inactive: ") ^ Int.toString m)
            ^ "]"
      in
      (((("Splitting : " ^ Print.decToString g (I.ctxDec g i)) ^ " (")
       ^ indexToString (index op))
      ^ flagToString (active (sl, 0), inactive (sl, 0)))
      ^ ")"

    let var ((_, i), _) = i
  end

  (* constCases (G, (V, s), I, abstract, C) = C'

       Invariant:
       If   G |- s : G'  G' |- V : type
       and  I a list of of constant declarations
       and  abstract an abstraction function
       and  C a list of possible cases
       then C' is a list extending C, containing all possible
         cases from I
    *)
  (* paramCases (G, (V, s), k, abstract, C) = C'

       Invariant:
       If   G |- s : G'  G' |- V : type
       and  k a variable
       and  abstract an abstraction function
       and  C a list of possible cases
       then C' is a list extending C, containing all possible
         cases introduced by parameters <= k in G
    *)
  (* lowerSplitDest (G, (V, s'), abstract) = C'

       Invariant:
       If   G0, G |- s' : G1  G1 |- V: type
       and  G is the context of local parameters
       and  abstract abstraction function
       then C' is a list of all cases unifying with V[s']
            (it contains constant and parameter cases)
    *)
  (* split ((G, M), (x:D, s), abstract) = C'

       Invariant :
       If   |- G ctx
       and  G |- M mtx
       and  G |- s : G1   and  G1 |- D : L
       and  abstract abstraction function
       then C' = (C1, ... Cn) are resulting cases from splitting D[s]
    *)
  (* rename to add N prefix? *)
  (* occursIn (k, U) = B,

       Invariant:
       If    U in nf
       then  B iff k occurs in U
    *)
  (* no case for Redex, EVar, EClo *)
  (* no case for FVar *)
  (* no case for SClo *)
  (* checkExp (M, U) = B

       Invariant:
       If   G |- M
       and  G |- U : V
       and  U in nf
       then B holds iff U does not contain any Bot variables
    *)
  (* copied from meta-abstract *)
  (* modeEq (marg, st) = B'

       Invariant:
       If   (marg = + and st = top) or (marg = - and st = bot)
       then B' = true
       else B' = false
    *)
  (*
       The inherit functions below copy the splitting depth attribute
       between successive states, using a simultaneous traversal
       in mode dependency Order.

       Invariant:
       (G,M,B) |- V type
       G = G0, G1, G2
       |G2| = k       (length of local context)
       d = |G1, G2|   (last BVar seen)
       let n < |G|
       if   n>d then n is an index of a variable already seen in mdo
       if   n=d then n is an index of a variable now seen for the first
                     time
       if   n<=k then n is a local parameter
       it is impossible for     k < n < d
    *)
  (* invariants on inheritXXX functions? -fp *)
  (* necessary for d' = 0 *)
  (* skip *)
  (* necessary for d = 0 *)
  (* Uni impossible *)
  (* new original variable *)
  (* inheritBelow (I.ctxLookup (B, n-k) - 1, k', V', (B', d-1, d')) *)
  (* already seen original variable *)
  (* then (B', d, d') *)
  (* previous line avoids redundancy,
                  but may violate invariant outside pattern fragment *)
  (* must correspond *)
  (* C' = BVar (n) *)
  (* C ~ C' *)
  (* n = k+d *)
  (* n' also new --- same variable: do not decrease *)
  (* n' not new --- decrease the splitting depth of all variables in V' *)
  (* cid = cid' *)
  (* cid = cid' *)
  (* mode dependency in Goal: first M.Top, then M.Bot *)
  (* S' *)
  (* current first occurrence depth in V *)
  (* current first occurrence depth in V' *)
  (* mode dependency in Clause: first M.Top then M.Bot *)
  (* check proper traversal *)
  (* abstractInit (M.State (name, M.Prefix (G, M, B), V)) = F'

       State is the state before splitting, to inherit splitting depths.
       Invariant:
       If   G |- V : L
       then forall |- G' ctx
            and    G' |- M' ctx
            and    G' |- s' : G
            and    names name'
            then   following holds: S' = F' (name', G', M', s')
                                    S' is a new state
    *)
  (* abstractInit (x:D, mode, F) = F'

       Invariant:
       If   G |- D : L
       and  forall |- G' ctx
            and    G' |- M' ctx
            and    G' |- s' : G
            and    names name'
            then   S' = F (name', G', M', s')
       then forall |- G' ctx
            and    G' |- M' ctx
            and    G' |- s' : G
            then   following holds: S' = F (name', (G', D[s]) , (M', mode) , 1 . s' o ^)
                                    is a new state
    *)
  (* expand' (M.Prefix (G, M), isIndex, abstract, makeAddress) = (M.Prefix (G', M'), s', ops')

       Invariant:
       If   |- G ctx
       and  G |- M mtx
       and  isIndex (k) = B function s.t. B holds iff k index
       and  abstract, dynamic abstraction function
       and  makeAddress, a function which calculates the index of the variable
            to be split
       then |- G' ctx
       and  G' |- M' mtx
       and  G' is a subcontext of G where all Top variables have been replaced
            by EVars'
       and  G' |- s' : G
       and  ops' is a list of all possiblie splitting operators
    *)
  (* check if splitting bound > 0 *)
  (* -###- *)
  (* b = 0 *)
  (* expand ((G, M), V) = ops'

       Invariant:
       If   |- G ctx
       and  G |- M mtx
       and  G |- V : L
       then ops' is a list of all possiblie splitting operators
    *)
  (* index (Op) = k

       Invariant:
       If   Op = (_, S) then k = |S|
    *)
  (* apply (Op) = Sl'

       Invariant:
       If   Op = (_, Sl) then Sl' = Sl
    *)
  (* menu (Op) = s'

       Invariant:
       If   Op = ((G, D), Sl)
       and  G |- D : L
       then s' = string describing the operator
    *)
  let expand = expand
  let apply = apply
  let var = var
  let index = index
  let menu = menu
end
(*! sharing Unify.IntSyn = MetaSyn'.IntSyn !*)
(*! structure CsManager : CS_MANAGER !*)
(*! sharing CsManager.IntSyn = MetaSyn'.IntSyn !*)
(* local *)
(* functor Splitting *)

(* # 1 "src/m2/Splitting.sml.ml" *)
