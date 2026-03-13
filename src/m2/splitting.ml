(* # 1 "src/m2/splitting.sig.ml" *)
open! Basis
open Metasyn

(* Splitting *)
(* Author: Carsten Schuermann *)
module type SPLITTING = sig
  module MetaSyn : METASYN

  exception Error of string

  type nonrec operator

  val expand : MetaSyn.state_ -> operator list
  val apply : operator -> MetaSyn.state_ list
  val var : operator -> int
  val menu : operator -> string
  val index : operator -> int
end
(* signature SPLITTING *)

(* # 1 "src/m2/splitting.fun.ml" *)
open! Basis
open Metasyn
open Meta_abstract
open Meta_print
open Modetable

(* Splitting *)
(* Author: Carsten Schuermann *)
module Splitting (Splitting__0 : sig
  module Global : GLOBAL
  module MetaSyn' : METASYN
  module MetaAbstract : METAABSTRACT with module MetaSyn = MetaSyn'
  module MetaPrint : METAPRINT with module MetaSyn = MetaSyn'
  module ModeTable : MODETABLE

  (*! sharing ModeSyn.IntSyn = MetaSyn'.IntSyn !*)
  module Whnf : WHNF

  (*! sharing Whnf.IntSyn = MetaSyn'.IntSyn !*)
  module Index : INDEX

  (*! sharing Index.IntSyn = MetaSyn'.IntSyn !*)
  module Print : PRINT

  (*! sharing Print.IntSyn = MetaSyn'.IntSyn !*)
  module Unify : UNIFY
end) : SPLITTING with module MetaSyn = Splitting__0.MetaSyn' = struct
  open Splitting__0
  module MetaSyn = MetaAbstract.MetaSyn

  exception Error of string

  (* Invariant:
     Case analysis generates a list of successor states
     (the cases) from a given state.

     'a flag marks cases where unification of the types
     succeeded as ""Active"", and cases where there were
     leftover constraints after unification as ""Inactive"".

     NB: cases where unification fails are not considered

     Consequence: Only those splitting operators can be
     applied which do not generate inactive cases.
  *)
  type 'a flag = Active of 'a | InActive
  type nonrec operator = (MetaSyn.state_ * int) * MetaSyn.state_ flag list

  open! struct
    module M = MetaSyn
    module I = IntSyn

    let rec constCases = function
      | g_, vs_, [], abstract, ops -> ops
      | g_, vs_, I.Const c :: sgn_, abstract, ops ->
          let u_, vs'_ = M.createAtomConst (g_, I.Const c) in
          constCases
            ( g_,
              vs_,
              sgn_,
              abstract,
              Cs_manager.trail (function () ->
                  (try
                     begin if Unify.unifiable (g_, vs_, vs'_) then
                       Active
                         (abstract (I.conDecName (I.sgnLookup c) ^ "/", u_))
                       :: ops
                     else ops
                     end
                   with MetaAbstract.Error _ -> InActive :: ops)) )

    let rec paramCases = function
      | g_, vs_, 0, abstract, ops -> ops
      | g_, vs_, k, abstract, ops ->
          let u_, vs'_ = M.createAtomBVar (g_, k) in
          paramCases
            ( g_,
              vs_,
              k - 1,
              abstract,
              Cs_manager.trail (function () ->
                  (try
                     begin if Unify.unifiable (g_, vs_, vs'_) then
                       Active (abstract (Int.toString k ^ "/", u_)) :: ops
                     else ops
                     end
                   with MetaAbstract.Error _ -> InActive :: ops)) )

    let rec lowerSplitDest = function
      | g_, ((I.Root (I.Const c, _) as v_), s'), abstract ->
          constCases
            ( g_,
              (v_, s'),
              Index.lookup c,
              abstract,
              paramCases (g_, (v_, s'), I.ctxLength g_, abstract, []) )
      | g_, (I.Pi ((d_, p_), v_), s'), abstract ->
          let d'_ = I.decSub (d_, s') in
          lowerSplitDest
            ( I.Decl (g_, d'_),
              (v_, I.dot1 s'),
              function name, u_ -> abstract (name, I.Lam (d'_, u_)) )

    let rec split (M.Prefix (g_, m_, b_), ((I.Dec (_, v_) as d_), s), abstract)
        =
      lowerSplitDest
        ( I.null_,
          (v_, s),
          function
          | name', u'_ ->
              abstract (name', M.Prefix (g_, m_, b_), I.Dot (I.Exp u'_, s)) )

    let rec occursInExp = function
      | k, I.Uni _ -> false
      | k, I.Pi (dp_, v_) -> occursInDecP (k, dp_) || occursInExp (k + 1, v_)
      | k, I.Root (c_, s_) -> occursInCon (k, c_) || occursInSpine (k, s_)
      | k, I.Lam (d_, v_) -> occursInDec (k, d_) || occursInExp (k + 1, v_)
      | k, I.FgnExp (csid_, fge_) ->
          I.FgnExpStd.fold (csid_, fge_)
            (function
              | u_, b_ -> b_ || occursInExp (k, Whnf.normalize (u_, I.id)))
            false

    and occursInCon = function
      | k, I.BVar k' -> k = k'
      | k, I.Const _ -> false
      | k, I.Def _ -> false
      | k, I.Skonst _ -> false

    and occursInSpine = function
      | _, nil_ -> false
      | k, I.App (u_, s_) -> occursInExp (k, u_) || occursInSpine (k, s_)

    and occursInDec (k, I.Dec (_, v_)) = occursInExp (k, v_)
    and occursInDecP (k, (d_, _)) = occursInDec (k, d_)

    let rec isIndexInit k = false
    let rec isIndexSucc (d_, isIndex) k = occursInDec (k, d_) || isIndex (k + 1)
    let rec isIndexFail (d_, isIndex) k = isIndex (k + 1)

    let rec checkVar = function
      | I.Decl (m_, M.Top), 1 -> true
      | I.Decl (m_, M.Bot), 1 -> false
      | I.Decl (m_, _), k -> checkVar (m_, k - 1)

    let rec checkExp = function
      | m_, I.Uni _ -> true
      | m_, I.Pi ((d_, p_), v_) ->
          checkDec (m_, d_) && checkExp (I.Decl (m_, M.Top), v_)
      | m_, I.Lam (d_, v_) ->
          checkDec (m_, d_) && checkExp (I.Decl (m_, M.Top), v_)
      | m_, I.Root (I.BVar k, s_) -> checkVar (m_, k) && checkSpine (m_, s_)
      | m_, I.Root (_, s_) -> checkSpine (m_, s_)

    and checkSpine = function
      | m_, I.Nil -> true
      | m_, I.App (u_, s_) -> checkExp (m_, u_) && checkSpine (m_, s_)

    and checkDec (m_, I.Dec (_, v_)) = checkExp (m_, v_)

    let rec modeEq = function
      | ModeSyn.Marg (plus_, _), M.Top -> true
      | ModeSyn.Marg (minus_, _), M.Bot -> true
      | _ -> false

    let rec inheritBelow = function
      | b', k', I.Lam (d'_, u'_), bdd'_ ->
          inheritBelow (b', k' + 1, u'_, inheritBelowDec (b', k', d'_, bdd'_))
      | b', k', I.Pi ((d'_, _), v'_), bdd'_ ->
          inheritBelow (b', k' + 1, v'_, inheritBelowDec (b', k', d'_, bdd'_))
      | b', k', I.Root (I.BVar n', s'_), (b'_, d, d') -> begin
          if n' = k' + d' && n' > k' then
            inheritBelowSpine (b', k', s'_, (I.Decl (b'_, b'), d, d' - 1))
          else inheritBelowSpine (b', k', s'_, (b'_, d, d'))
        end
      | b', k', I.Root (c_, s'_), bdd'_ -> inheritBelowSpine (b', k', s'_, bdd'_)

    and inheritBelowSpine = function
      | b', k', nil_, bdd'_ -> bdd'_
      | b', k', I.App (u'_, s'_), bdd'_ ->
          inheritBelowSpine (b', k', s'_, inheritBelow (b', k', u'_, bdd'_))

    and inheritBelowDec (b', k', I.Dec (x, v'_), bdd'_) =
      inheritBelow (b', k', v'_, bdd'_)

    let rec skip = function
      | k, I.Lam (d_, u_), bdd'_ -> skip (k + 1, u_, skipDec (k, d_, bdd'_))
      | k, I.Pi ((d_, _), v_), bdd'_ -> skip (k + 1, v_, skipDec (k, d_, bdd'_))
      | k, I.Root (I.BVar n, s_), (b'_, d, d') -> begin
          if n = k + d && n > k then skipSpine (k, s_, (b'_, d - 1, d'))
          else skipSpine (k, s_, (b'_, d, d'))
        end
      | k, I.Root (c_, s_), bdd'_ -> skipSpine (k, s_, bdd'_)

    and skipSpine = function
      | k, nil_, bdd'_ -> bdd'_
      | k, I.App (u_, s_), bdd'_ -> skipSpine (k, s_, skip (k, u_, bdd'_))

    and skipDec (k, I.Dec (x, v_), bdd'_) = skip (k, v_, bdd'_)

    let rec inheritExp = function
      | b_, k, I.Lam (d_, u_), k', I.Lam (d'_, u'_), bdd'_ ->
          inheritExp
            (b_, k + 1, u_, k' + 1, u'_, inheritDec (b_, k, d_, k', d'_, bdd'_))
      | b_, k, I.Pi ((d_, _), v_), k', I.Pi ((d'_, _), v'_), bdd'_ ->
          inheritExp
            (b_, k + 1, v_, k' + 1, v'_, inheritDec (b_, k, d_, k', d'_, bdd'_))
      | b_, k, (I.Root (I.BVar n, s_) as v_), k', v'_, (b'_, d, d') -> begin
          if n = k + d && n > k then
            skipSpine
              ( k,
                s_,
                inheritNewRoot
                  (b_, I.ctxLookup (b_, n - k), k, v_, k', v'_, (b'_, d, d')) )
          else begin
            if n > k + d then
              skipSpine
                ( k,
                  s_,
                  inheritBelow
                    (I.ctxLookup (b_, n - k) - 1, k', v'_, (b'_, d, d')) )
            else
              let (I.Root (c'_, s'_)) = v'_ in
              inheritSpine (b_, k, s_, k', s'_, (b'_, d, d'))
          end
        end
      | b_, k, I.Root (c_, s_), k', I.Root (c'_, s'_), bdd'_ ->
          inheritSpine (b_, k, s_, k', s'_, bdd'_)

    and inheritNewRoot = function
      | ( b_,
          b,
          k,
          I.Root (I.BVar n, s_),
          k',
          (I.Root (I.BVar n', s'_) as v'_),
          (b'_, d, d') ) -> begin
          if n' = k' + d' && n' > k' then
            inheritBelow (b, k', v'_, (b'_, d - 1, d'))
          else inheritBelow (b - 1, k', v'_, (b'_, d - 1, d'))
        end
      | b_, b, k, v_, k', v'_, (b'_, d, d') ->
          inheritBelow (b - 1, k', v'_, (b'_, d - 1, d'))

    and inheritSpine = function
      | b_, k, I.Nil, k', I.Nil, bdd'_ -> bdd'_
      | b_, k, I.App (u_, s_), k', I.App (u'_, s'_), bdd'_ ->
          inheritSpine
            (b_, k, s_, k', s'_, inheritExp (b_, k, u_, k', u'_, bdd'_))

    and inheritDec (b_, k, I.Dec (_, v_), k', I.Dec (_, v'_), bdd'_) =
      inheritExp (b_, k, v_, k', v'_, bdd'_)

    let rec inheritDTop = function
      | ( b_,
          k,
          I.Pi ((I.Dec (_, v1_), I.No), v2_),
          k',
          I.Pi ((I.Dec (_, v1'_), I.No), v2'_),
          bdd'_ ) ->
          inheritG
            ( b_,
              k,
              v1_,
              k',
              v1'_,
              inheritDTop (b_, k + 1, v2_, k' + 1, v2'_, bdd'_) )
      | ( b_,
          k,
          (I.Root (I.Const cid, s_) as v_),
          k',
          (I.Root (I.Const cid', s'_) as v'_),
          bdd'_ ) ->
          let mS = valOf (ModeTable.modeLookup cid) in
          inheritSpineMode (M.Top, mS, b_, k, s_, k', s'_, bdd'_)

    and inheritDBot = function
      | ( b_,
          k,
          I.Pi ((I.Dec (_, v1_), I.No), v2_),
          k',
          I.Pi ((I.Dec (_, v1'_), I.No), v2'_),
          bdd'_ ) ->
          inheritDBot (b_, k + 1, v2_, k' + 1, v2'_, bdd'_)
      | b_, k, I.Root (I.Const cid, s_), k', I.Root (I.Const cid', s'_), bdd'_
        ->
          let mS = valOf (ModeTable.modeLookup cid) in
          inheritSpineMode (M.Bot, mS, b_, k, s_, k', s'_, bdd'_)

    and inheritG
        ( b_,
          k,
          I.Root (I.Const cid, s_),
          k',
          (I.Root (I.Const cid', s'_) as v'_),
          bdd'_ ) =
      let mS = valOf (ModeTable.modeLookup cid) in
      inheritSpineMode
        ( M.Bot,
          mS,
          b_,
          k,
          s_,
          k',
          s'_,
          inheritSpineMode (M.Top, mS, b_, k, s_, k', s'_, bdd'_) )

    and inheritSpineMode = function
      | mode, ModeSyn.Mnil, b_, k, I.Nil, k', I.Nil, bdd'_ -> bdd'_
      | ( mode,
          ModeSyn.Mapp (m, mS),
          b_,
          k,
          I.App (u_, s_),
          k',
          I.App (u'_, s'_),
          bdd'_ ) -> begin
          if modeEq (m, mode) then
            inheritSpineMode
              ( mode,
                mS,
                b_,
                k,
                s_,
                k',
                s'_,
                inheritExp (b_, k, u_, k', u'_, bdd'_) )
          else inheritSpineMode (mode, mS, b_, k, s_, k', s'_, bdd'_)
        end

    let rec inheritSplitDepth
        ( (M.State (_, M.Prefix (g_, m_, b_), v_) as s_),
          (M.State (name', M.Prefix (g'_, m'_, b'_), v'_) as s'_) ) =
      let d = I.ctxLength g_ in
      let d' = I.ctxLength g'_ in
      let v_ = Whnf.normalize (v_, I.id) in
      let v'_ = Whnf.normalize (v'_, I.id) in
      let b''_, 0, 0 =
        inheritDBot
          (b_, 0, v_, 0, v'_, inheritDTop (b_, 0, v_, 0, v'_, (I.null_, d, d')))
      in
      M.State (name', M.Prefix (g'_, m'_, b''_), v'_)

    let rec abstractInit (M.State (name, gm_, v_))
        (name', M.Prefix (g'_, m'_, b'_), s') =
      inheritSplitDepth
        ( M.State (name, gm_, v_),
          MetaAbstract.abstract
            (M.State (name ^ name', M.Prefix (g'_, m'_, b'_), I.EClo (v_, s')))
        )

    let rec abstractCont ((d_, mode, b), abstract)
        (name', M.Prefix (g'_, m'_, b'_), s') =
      abstract
        ( name',
          M.Prefix
            ( I.Decl (g'_, I.decSub (d_, s')),
              I.Decl (m'_, mode),
              I.Decl (b'_, b) ),
          I.dot1 s' )

    let rec makeAddressInit s_ k = (s_, k)
    let rec makeAddressCont makeAddress k = makeAddress (k + 1)

    let rec expand' = function
      | M.Prefix (I.Null, I.Null, I.Null), isIndex, abstract, makeAddress ->
          (M.Prefix (I.Null, I.Null, I.Null), I.id, [])
      | ( M.Prefix
            (I.Decl (g_, d_), I.Decl (m_, (M.Top as mode)), I.Decl (b_, b)),
          isIndex,
          abstract,
          makeAddress ) ->
          let M.Prefix (g'_, m'_, b'_), s', ops =
            expand'
              ( M.Prefix (g_, m_, b_),
                isIndexSucc (d_, isIndex),
                abstractCont ((d_, mode, b), abstract),
                makeAddressCont makeAddress )
          in
          let (I.Dec (xOpt, v_)) = d_ in
          let x_ = I.newEVar (g'_, I.EClo (v_, s')) in
          let ops' =
            begin if b > 0 && (not (isIndex 1)) && checkDec (m_, d_) then
              ( makeAddress 1,
                split (M.Prefix (g'_, m'_, b'_), (d_, s'), abstract) )
              :: ops
            else ops
            end
          in
          (M.Prefix (g'_, m'_, b'_), I.Dot (I.Exp x_, s'), ops')
      | ( M.Prefix
            (I.Decl (g_, d_), I.Decl (m_, (M.Bot as mode)), I.Decl (b_, b)),
          isIndex,
          abstract,
          makeAddress ) ->
          let M.Prefix (g'_, m'_, b'_), s', ops =
            expand'
              ( M.Prefix (g_, m_, b_),
                isIndexSucc (d_, isIndex),
                abstractCont ((d_, mode, b), abstract),
                makeAddressCont makeAddress )
          in
          ( M.Prefix
              ( I.Decl (g'_, I.decSub (d_, s')),
                I.Decl (m'_, M.Bot),
                I.Decl (b'_, b) ),
            I.dot1 s',
            ops )

    let rec expand (M.State (name, M.Prefix (g_, m_, b_), v_) as s_) =
      let _, _, ops =
        expand'
          ( M.Prefix (g_, m_, b_),
            isIndexInit,
            abstractInit s_,
            makeAddressInit s_ )
      in
      ops

    let rec index (_, sl_) = List.length sl_

    let rec apply (_, sl_) =
      map
        (function
          | Active s_ -> s_
          | InActive -> raise (Error "Not applicable: leftover constraints"))
        sl_

    let rec menu (((M.State (name, M.Prefix (g_, m_, b_), v_), i), sl_) as op_)
        =
      let rec active = function
        | [], n -> n
        | InActive :: l_, n -> active (l_, n)
        | Active _ :: l_, n -> active (l_, n + 1)
      in
      let rec inactive = function
        | [], n -> n
        | InActive :: l_, n -> inactive (l_, n + 1)
        | Active _ :: l_, n -> inactive (l_, n)
      in
      let rec indexToString = function
        | 0 -> "zero cases"
        | 1 -> "1 case"
        | n -> Int.toString n ^ " cases"
      in
      let rec flagToString = function
        | _, 0 -> ""
        | n, m ->
            (((" [active: " ^ Int.toString n) ^ " inactive: ") ^ Int.toString m)
            ^ "]"
      in
      (((("Splitting : " ^ Print.decToString (g_, I.ctxDec (g_, i))) ^ " (")
       ^ indexToString (index op_))
      ^ flagToString (active (sl_, 0), inactive (sl_, 0)))
      ^ ")"

    let rec var ((_, i), _) = i
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
       in mode dependency order.

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
(*! structure Cs_manager : CS_MANAGER !*)
(*! sharing Cs_manager.IntSyn = MetaSyn'.IntSyn !*)
(* local *)
(* functor Splitting *)

(* # 1 "src/m2/splitting.sml.ml" *)
