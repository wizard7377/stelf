open! Global.Global_
open! Intsyn.Lambda_
open! Subordinate
open! Typecheck.Typecheck_

(* # 1 "src/meta/Abstract.sig.ml" *)
open Funsyn
open Statesyn
open Funtypecheck

(* Meta Theorem Prover abstraction : Version 1.3 *)
(* Author: Frank Pfenning, Carsten Schuermann *)
include MTPABSTRACT
(* signature MTPABSTRACT *)

(* # 1 "src/meta/Abstract.fun.ml" *)
open! Basis

(* Meta Theorem Prover abstraction : Version 1.3 *)
(* Author: Frank Pfenning, Carsten Schuermann *)
exception Error of string

let () =
  Printexc.register_printer (function Error msg -> Some msg | _ -> None)

module MTPAbstract (MTPAbstract__0 : sig
  (*! structure IntSyn' : INTSYN !*)
  (*! structure FunSyn' : FUNSYN !*)
  (*! sharing FunSyn'.IntSyn = IntSyn' !*)
  module StateSyn' : STATESYN.STATESYN

  (*! sharing StateSyn'.FunSyn = FunSyn' !*)
  module Whnf : WHNF

  (*! sharing Whnf.IntSyn = IntSyn' !*)
  module Constraints : CONSTRAINTS

  (*! sharing Constraints.IntSyn = IntSyn' !*)
  module Unify : UNIFY

  (*! sharing Unify.IntSyn = IntSyn' !*)
  module Subordinate : Subordinate_.SUBORDINATE

  (*! sharing Subordinate.IntSyn = IntSyn' !*)
  module TypeCheck : TYPECHECK

  (*! sharing TypeCheck.IntSyn = IntSyn' !*)
  module FunTypeCheck : FUNTYPECHECK.FUNTYPECHECK

  (*! sharing FunTypeCheck.FunSyn = FunSyn' !*)
  module Abstract : ABSTRACT
end) : MTPABSTRACT.MTPABSTRACT = struct
  (*! structure IntSyn = IntSyn' !*)
  (*! structure FunSyn = FunSyn' !*)
  open MTPAbstract__0
  module StateSyn = StateSyn'

  exception Error = Error

  type approxFor =
    | Head of IntSyn.dctx * (FunSyn.for_ * IntSyn.sub) * int
    | Block of (IntSyn.dctx * IntSyn.sub * int * IntSyn.dec list) * approxFor

  (* Approximat formula *)
  (* AF ::= F [s] *)
  (*      | (t, G2), AF *)
  open! struct
    module I = IntSyn
    module F = FunSyn
    module S = StateSyn
    module C = Constraints

    type eBVar =
      | Ev of I.exp option ref * I.exp * S.tag * int
      | Bv of I.dec * S.tag

    let checkEmpty = function
      | [] -> ()
      | cnstrL ->
          begin match C.simplify cnstrL with
          | [] -> ()
          | _ -> raise (Error "Typing ambiguous -- unresolved constraints")
          end

    let eqEVar arg__1 arg__2 =
      begin match (arg__1, arg__2) with
      | I.EVar (r1, _, _, _), Ev (r2, _, _, _) -> r1 == r2
      | _, _ -> false
      end

    let exists p k =
      let rec exists' = function
        | I.Null -> false
        | I.Decl (k', y) -> p y || exists' k'
      in
      exists' k

    let ( or ) = function
      | I.Maybe, _ -> I.Maybe
      | _, I.Maybe -> I.Maybe
      | I.Meta, _ -> I.Meta
      | _, I.Meta -> I.Meta
      | I.No, I.No -> I.No

    let rec occursInExp (k, a) = match a with
      | I.Uni _ -> I.No
      | I.Pi (dp, v) ->
          ( or ) (occursInDecP (k, dp), occursInExp (k + 1, v))
      | I.Root (h, s) -> occursInHead (k, h, occursInSpine (k, s))
      | I.Lam (d, v) ->
          ( or ) (occursInDec (k, d), occursInExp (k + 1, v))

    and occursInHead (k, a, dp) = match a, dp with
      | I.BVar k', dp ->
          begin if k = k' then I.Maybe else dp
          end
      | I.Const _, dp -> dp
      | I.Def _, dp -> dp
      | I.Skonst _, I.No -> I.No
      | I.Skonst _, I.Meta -> I.Meta
      | I.Skonst _, I.Maybe -> I.Meta

    and occursInSpine (k, a) = match a with
      | I.Nil -> I.No
      | I.App (u, s) -> ( or ) (occursInExp (k, u), occursInSpine (k, s))

    and occursInDec (k, I.Dec (_, v)) = occursInExp (k, v)
    and occursInDecP (k, (d, _)) = occursInDec (k, d)

    let piDepend a1 a2 b1 = match (a1, a2), b1 with
      | (d, I.No), v -> I.Pi ((d, I.No), v)
      | (d, I.Meta), v -> I.Pi ((d, I.Meta), v)
      | (d, I.Maybe), v -> I.Pi ((d, occursInExp (1, v)), v)

    let rec weaken a1 b1 = match a1, b1 with
      | I.Null, a -> I.id
      | I.Decl (g', (I.Dec (name, v) as d)), a ->
          let w' = weaken g' a in
          begin if Subordinate.belowEq (I.targetFam v) a then I.dot1 w'
          else I.comp w' I.shift
          end

    let rec raiseType a1 b1 = match a1, b1 with
      | I.Null, v -> v
      | I.Decl (g, d), v -> raiseType g (I.Pi ((d, I.Maybe), v))

    let rec restore = function
      | 0, gp -> (gp, I.Null)
      | n, I.Decl (g, d) ->
          let gp', gx' = restore (n - 1, g) in
          (gp', I.Decl (gx', d))

    let rec concat (gp, a) = match a with
      | I.Null -> gp
      | I.Decl (g, d) -> I.Decl (concat (gp, g), d)

    let rec collectExpW (tag, d, g, a, k) = match a with
      | (I.Uni l, s) -> k
      | (I.Pi ((d_, _), v), s) ->
          collectExp
            ( tag,
              d,
              I.Decl (g, I.decSub d_ s),
              (v, I.dot1 s),
              collectDec (tag, d, g, (d_, s), k) )
      | (I.Root (_, s_), s) ->
          collectSpine (S.decrease tag, d, g, (s_, s), k)
      | (I.Lam (d_, u), s) ->
          collectExp
            ( tag,
              d,
              I.Decl (g, I.decSub d_ s),
              (u, I.dot1 s),
              collectDec (tag, d, g, (d_, s), k) )
      | ((I.EVar (r, gdX, v, cnstrs) as x), s) ->
          begin if exists (eqEVar x) k then collectSub (tag, d, g, s, k)
          else
            let gp, gx = restore (I.ctxLength gdX - d, gdX) in
            ignore (checkEmpty !cnstrs);
            let w = weaken gx (I.targetFam v) in
            let iw = Whnf.invert w in
            let gx' = Whnf.strengthen iw gx in
            let (I.EVar (r', _, _, _) as x') =
              I.newEVar (concat (gp, gx')) (I.EClo (v, iw))
            in
            ignore (Unify.instantiateEVar r (I.EClo (x', w)) []);
            let v' = raiseType gx' (I.EClo (v, iw)) in
            collectSub
              ( tag,
                d,
                g,
                I.comp w s,
                I.Decl
                  ( collectExp (tag, d, gp, (v', I.id), k),
                    Ev (r', v', tag, d) ) )
          end
      | (I.FgnExp (csid, csfe), s) ->
          I.FgnExpStd.fold csid csfe
            (function u, k' -> collectExp (tag, d, g, (u, s), k'))
            k

    and collectExp (tag, d, g, us, k) =
      collectExpW (tag, d, g, Whnf.whnf us, k)

    and collectSpine (tag, d, g, a, k) = match a with
      | (I.Nil, _) -> k
      | (I.SClo (s_, s'), s) ->
          collectSpine (tag, d, g, (s_, I.comp s' s), k)
      | (I.App (u, s_), s) ->
          collectSpine
            (tag, d, g, (s_, s), collectExp (tag, d, g, (u, s), k))

    and collectDec (tag, d, g, (I.Dec (_, v), s), k) =
      collectExp (tag, d, g, (v, s), k)

    and collectSub (tag, d, g, a, k) = match a with
      | I.Shift _ -> k
      | I.Dot (I.Idx _, s) -> collectSub (tag, d, g, s, k)
      | I.Dot (I.Exp u, s) ->
          collectSub (tag, d, g, s, collectExp (tag, d, g, (u, I.id), k))

    let rec abstractEVar (a, depth, b) = match a, b with
      | I.Decl (k', Ev (r', _, _, d)), (I.EVar (r, _, _, _) as x) ->
          begin if r == r' then (I.BVar (depth + 1), d)
          else abstractEVar (k', depth + 1, x)
          end
      | I.Decl (k', Bv _), x -> abstractEVar (k', depth + 1, x)

    let lookupBV (k_, i) =
      let rec lookupBV' (a, i, k) = match a, i with
        | I.Decl (k_, Ev (r, v, _, _)), i -> lookupBV' (k_, i, k + 1)
        | I.Decl (k_, Bv _), 1 -> k
        | I.Decl (k_, Bv _), i -> lookupBV' (k_, i - 1, k + 1)
      in
      lookupBV' (k_, i, 1)

    let rec abstractExpW (k_, depth, a) = match a with
      | ((I.Uni l as u), s) -> u
      | (I.Pi ((d, p), v), s) ->
          piDepend
            (abstractDec (k_, depth, (d, s))) p (abstractExp (k_, depth + 1, (v, I.dot1 s)))
      | (I.Root ((I.BVar k as h), s_), s) ->
          begin if k > depth then
            let k' = lookupBV (k_, k - depth) in
            I.Root (I.BVar (k' + depth), abstractSpine (k_, depth, (s_, s)))
          else I.Root (h, abstractSpine (k_, depth, (s_, s)))
          end
      | (I.Root (h, s_), s) ->
          I.Root (h, abstractSpine (k_, depth, (s_, s)))
      | (I.Lam (d, u), s) ->
          I.Lam
            ( abstractDec (k_, depth, (d, s)),
              abstractExp (k_, depth + 1, (u, I.dot1 s)) )
      | ((I.EVar (_, g, _, _) as x), s) ->
          let h, d = abstractEVar (k_, depth, x) in
          I.Root (h, abstractSub (I.ctxLength g - d, k_, depth, s, I.Nil))
      | (I.FgnExp (csid, csfe), s) ->
          I.FgnExpStd.Map.apply csid csfe (function u ->
              abstractExp (k_, depth, (u, s)))

    and abstractExp (k, depth, us) = abstractExpW (k, depth, Whnf.whnf us)

    and abstractSub (n, k_, depth, a, s_) = match a with
      | I.Shift k ->
          begin if n > 0 then
            abstractSub
              (n, k_, depth, I.Dot (I.Idx (k + 1), I.Shift (k + 1)), s_)
          else s_
          end
      | I.Dot (I.Idx k, s) ->
          let h =
            begin if k > depth then
              let k' = lookupBV (k_, k - depth) in
              I.BVar (k' + depth)
            else I.BVar k
            end
          in
          abstractSub (n - 1, k_, depth, s, I.App (I.Root (h, I.Nil), s_))
      | I.Dot (I.Exp u, s) ->
          abstractSub
            ( n - 1,
              k_,
              depth,
              s,
              I.App (abstractExp (k_, depth, (u, I.id)), s_) )

    and abstractSpine (k, depth, a) = match a with
      | (I.Nil, _) -> I.Nil
      | (I.SClo (s_, s'), s) ->
          abstractSpine (k, depth, (s_, I.comp s' s))
      | (I.App (u, s_), s) ->
          I.App
            ( abstractExp (k, depth, (u, s)),
              abstractSpine (k, depth, (s_, s)) )

    and abstractDec (k, depth, (I.Dec (x, v), s)) =
      I.Dec (x, abstractExp (k, depth, (v, s)))

    let rec getLevel = function
      | I.Uni _ -> I.Kind
      | I.Pi (_, u) -> getLevel u
      | I.Root _ -> I.Type
      | I.Redex (u, _) -> getLevel u
      | I.Lam (_, u) -> getLevel u
      | I.EClo (u, _) -> getLevel u

    let checkType v =
      begin match getLevel v with
      | I.Type -> ()
      | _ -> raise (Error "Typing ambiguous -- free type variable")
      end

    let rec abstractCtx = function
      | I.Null -> (I.Null, I.Null)
      | I.Decl (k', Ev (_, v', (S.Lemma _b as t), _)) ->
          let v'' = abstractExp (k', 0, (v', I.id)) in
          ignore (checkType v'');
          let g', b' = abstractCtx k' in
          let d' = I.Dec (None, v'') in
          (I.Decl (g', d'), I.Decl (b', t))
      | I.Decl (k', Ev (_, v', (S.None as t), _)) ->
          let v'' = abstractExp (k', 0, (v', I.id)) in
          ignore (checkType v'');
          let g', b' = abstractCtx k' in
          let d' = I.Dec (None, v'') in
          (I.Decl (g', d'), I.Decl (b', S.None))
      | I.Decl (k', Bv (d, tag)) ->
          let d' = abstractDec (k', 0, (d, I.id)) in
          let g', b' = abstractCtx k' in
          (I.Decl (g', d'), I.Decl (b', tag))

    let rec abstractGlobalSub (k_, a, b) = match a, b with
      | I.Shift _, I.Null -> I.Shift (I.ctxLength k_)
      | I.Shift n, (I.Decl _ as b) ->
          abstractGlobalSub (k_, I.Dot (I.Idx (n + 1), I.Shift (n + 1)), b)
      | I.Dot (I.Idx k, s'), I.Decl (b, (S.Parameter _ as t)) ->
          I.Dot (I.Idx (lookupBV (k_, k)), abstractGlobalSub (k_, s', b))
      | I.Dot (I.Exp u, s'), I.Decl (b, (S.Lemma _ as t)) ->
          I.Dot
            ( I.Exp (abstractExp (k_, 0, (u, I.id))),
              abstractGlobalSub (k_, s', b) )

    let rec collectGlobalSub (g0, a, b, collect) = match a, b with
      | I.Shift _, I.Null -> collect
      | s, (I.Decl (_, S.Parameter (Some l)) as b) ->
          let (F.LabelDec (name, _, g2)) = F.labelLookup l in
          skip (g0, List.length g2, s, b, collect)
      | I.Dot (I.Exp u, s), I.Decl (b, tag) ->
          collectGlobalSub
            ( g0,
              s,
              b,
              function
              | d, k -> collect (d, collectExp (tag, d, g0, (u, I.id), k))
            )

    and skip (a, n, s, b, collect) = match a, n, b with
      | g0, 0, b -> collectGlobalSub (g0, s, b, collect)
      | I.Decl (g0, d_), n, I.Decl (b, (S.Parameter _ as t)) ->
          skip
            ( g0,
              n - 1,
              I.invDot1 s,
              b,
              function d, k -> collect (d + 1, I.Decl (k, Bv (d_, t))) )

    let abstractNew ((g0, b0), s, b) =
      let cf = collectGlobalSub (g0, s, b, function _, k' -> k') in
      let k = cf (0, I.Null) in
      (abstractCtx k, abstractGlobalSub (k, s, b))

    let abstractSubAll (t, b1, (g0, b0), s, b) =
      let rec skip'' (k, a) = match a with
        | (I.Null, I.Null) -> k
        | (I.Decl (g0, d), I.Decl (b0, tag)) ->
            I.Decl (skip'' (k, (g0, b0)), Bv (d, tag))
      in
      let collect2 = collectGlobalSub (g0, s, b, function _, k' -> k') in
      let collect0 =
        collectGlobalSub (I.Null, t, b1, function _, k' -> k')
      in
      let k0 = collect0 (0, I.Null) in
      let k1 = skip'' (k0, (g0, b0)) in
      let d = I.ctxLength g0 in
      let k = collect2 (d, k1) in
      (abstractCtx k, abstractGlobalSub (k, s, b))

    let rec abstractFor (k, depth, a) = match a with
      | (F.All (F.Prim d, f), s) ->
          F.All
            ( F.Prim (abstractDec (k, depth, (d, s))),
              abstractFor (k, depth + 1, (f, I.dot1 s)) )
      | (F.Ex (d, f), s) ->
          F.Ex
            ( abstractDec (k, depth, (d, s)),
              abstractFor (k, depth + 1, (f, I.dot1 s)) )
      | (True, s) -> F.True
      | (F.And (f1, f2), s) ->
          F.And
            ( abstractFor (k, depth, (f1, s)),
              abstractFor (k, depth, (f2, s)) )

    let rec allClo (a, f) = match a with
      | I.Null -> f
      | I.Decl (gx, d) -> allClo (gx, F.All (F.Prim d, f))

    let rec convert = function
      | I.Null -> I.Null
      | I.Decl (g, d) -> I.Decl (convert g, Bv (d, S.Parameter None))

    let rec createEmptyB = function
      | 0 -> I.Null
      | n -> I.Decl (createEmptyB (n - 1), S.None)

    let rec lower = function
      | _, 0 -> I.Null
      | I.Decl (g, d), n -> I.Decl (lower (g, n - 1), d)

    let rec split = function
      | g, 0 -> (g, I.Null)
      | I.Decl (g, d), n ->
          let g1, g2 = split (g, n - 1) in
          (g1, I.Decl (g2, d))

    let rec shift = function
      | I.Null -> I.shift
      | I.Decl (g, _) -> I.dot1 (shift g)

    let rec ctxSub (a, s) = match a with
      | [] -> []
      | d :: g -> I.decSub d s :: ctxSub (g, I.dot1 s)

    let rec weaken2 (b, a, i) = match b with
      | I.Null -> (I.id, function s -> s)
      | I.Decl (g', (I.Dec (name, v) as d)) ->
          let w', s' = weaken2 (g', a, i + 1) in
          begin if Subordinate.belowEq (I.targetFam v) a then
            (I.dot1 w', function s -> I.App (I.Root (I.BVar i, I.Nil), s))
          else (I.comp w' I.shift, s')
          end

    let rec raiseType a1 b1 = match a1, b1 with
      | I.Null, v -> v
      | I.Decl (g, d), v ->
          raiseType
            g (Abstract.piDepend (Whnf.normalizeDec d I.id) I.Maybe v)

    let rec raiseFor (k, gorig, a, w, sc) = match a with
      | (F.True as f) -> f
      | F.Ex (I.Dec (name, v), f) ->
          let g_ = F.listToCtx (ctxSub (F.ctxToList gorig, w)) in
          let g = I.ctxLength g_ in
          let s = sc (w, k) in
          let v' = I.EClo (v, s) in
          let nw, s = weaken2 (g_, I.targetFam v, 1) in
          let iw = Whnf.invert nw in
          let gw = Whnf.strengthen iw g_ in
          let v'' = Whnf.normalize (v', iw) in
          let v''' = Whnf.normalize (raiseType gw v'', I.id) in
          let s''' = s I.Nil in
          let sc' (w', k') =
                let s' = sc (w', k') in
                I.Dot (I.Exp (I.Root (I.BVar (g + k' - k), s''')), s')
          in
          let f' = raiseFor (k + 1, gorig, f, I.comp w I.shift, sc') in
          F.Ex (I.Dec (name, v'''), f')
      | F.All (F.Prim (I.Dec (name, v)), f) ->
          let g_ = F.listToCtx (ctxSub (F.ctxToList gorig, w)) in
          let g = I.ctxLength g_ in
          let s = sc (w, k) in
          let v' = I.EClo (v, s) in
          let nw, s = weaken2 (g_, I.targetFam v, 1) in
          let iw = Whnf.invert nw in
          let gw = Whnf.strengthen iw g_ in
          let v'' = Whnf.normalize (v', iw) in
          let v''' = Whnf.normalize (raiseType gw v'', I.id) in
          let s''' = s I.Nil in
          let sc' (w', k') =
                let s' = sc (w', k') in
                I.Dot (I.Exp (I.Root (I.BVar (g + k' - k), s''')), s')
          in
          let f' = raiseFor (k + 1, gorig, f, I.comp w I.shift, sc') in
          F.All (F.Prim (I.Dec (name, v''')), f')

    let rec extend (k, a) = match a with
      | [] -> k
      | d :: l -> extend (I.Decl (k, Bv (d, S.None)), l)

    let rec makeFor (k_, w, a) = match a with
      | Head (g, (f, s), d) ->
          let cf =
            collectGlobalSub (g, s, createEmptyB d, function _, k' -> k')
          in
          let k = I.ctxLength k_ in
          let k'_ = cf (I.ctxLength g, k_) in
          let k' = I.ctxLength k'_ in
          let gk, bk = abstractCtx k'_ in
          ignore begin if !Global.doubleCheck then TypeCheck.typeCheckCtx gk else ()
            end;
          let w' = I.comp w (I.Shift (k' - k)) in
          let fk = abstractFor (k'_, 0, (f, s)) in
          ignore begin if !Global.doubleCheck then FunTypeCheck.isFor gk fk
            else ()
            end;
          let gk1, gk2 = split (gk, k' - k) in
          (gk1, allClo (gk2, fk))
      | Block ((g, t, d, g2), af) ->
          let k = I.ctxLength k_ in
          let collect =
            collectGlobalSub (g, t, createEmptyB d, function _, k' -> k')
          in
          let k'_ = collect (I.ctxLength g, k_) in
          let k' = I.ctxLength k'_ in
          let k'' = extend (k'_, g2) in
          let w' = F.dot1n (F.listToCtx g2) (I.comp w (I.Shift (k' - k))) in
          let gk, f' = makeFor (k'', w', af) in
          ignore begin if !Global.doubleCheck then FunTypeCheck.isFor gk f'
            else ()
            end;
          let gk1, gk2 = split (gk, List.length g2) in
          let f'' =
            raiseFor (0, gk2, f', I.id, function w, _ -> F.dot1n gk2 w)
          in
          ignore begin if !Global.doubleCheck then FunTypeCheck.isFor gk1 f''
            else ()
            end;
          let gk11, gk12 = split (gk1, k' - k) in
          let f''' = allClo (gk12, f'') in
          ignore begin if !Global.doubleCheck then FunTypeCheck.isFor gk11 f'''
            else ()
            end;
          (gk11, f''')

    let abstractApproxFor = function
      | Head (g, _, _) as af ->
          let _, f = makeFor (convert g, I.id, af) in
          f
      | Block ((g, _, _, _), _) as af ->
          let _, f = makeFor (convert g, I.id, af) in
          f
  end

  (* Intermediate Data Structure *)
  (* y ::= (X , {G2} V)  if {G1, G2 |- X : V
                                          |G1| = d *)
  (*
       We write {{K}} for the context of K, where EVars and BVars have
       been translated to declarations and their occurrences to BVars.
       We write {{U}}_K, {{S}}_K for the corresponding translation of an
       expression or spine.

       Just like contexts G, any K is implicitly assumed to be
       well-formed and in dependency Order.

       We write  K ||- U  if all EVars and BVars in U are collected in K.
       In particular, . ||- U means U contains no EVars or BVars.  Similarly,
       for spines K ||- S and other syntactic categories.

       Collection and abstraction raise Error if there are unresolved
       constraints after simplification.
    *)
  (* checkEmpty Cnstr = ()
       raises Error exception if constraints Cnstr cannot be simplified
       to the empty constraint
    *)
  (* eqEVar X Y = B
       where B iff X and Y represent same variable
    *)
  (* exists P K = B
       where B iff K = K1, Y, K2  s.t. P Y  holds
    *)
  (* occursInExp (k, U) = DP,

       Invariant:
       If    U in nf
       then  DP = No      iff k does not occur in U
             DP = Maybe   iff k occurs in U some place not as an argument to a Skonst
             DP = Meta    iff k occurs in U and only as arguments to Skonsts
    *)
  (* no case for Redex, EVar, EClo *)
  (* no case for FVar *)
  (* no case for SClo *)
  (* piDepend ((D,P), V) = Pi ((D,P'), V)
       where P' = Maybe if D occurs in V, P' = No otherwise
    *)
  (* optimize to have fewer traversals? -cs *)
  (* pre-Stelf 1.2 code walk Fri May  8 11:17:10 1998 *)
  (* weaken (depth,  G, a) = (w')
    *)
  (* raiseType (G, V) = {{G}} V

       Invariant:
       If G |- V : L
       then  . |- {{G}} V : L

       All abstractions are potentially dependent.
    *)
  (* collectExpW (tag_, d, G, (U, s), K) = K'

       Invariant:
       If    G |- s : G1     G1 |- U : V      (U,s) in whnf
       No circularities in U
             (enforced by extended occurs-check for BVars in Unify)
       and   K' = K, K''
             where K'' contains all EVars and BVars in (U,s)
    *)
  (* Possible optimization: Calculate also the normal form of the term *)
  (* optimization possible for d = 0 *)
  (* hack - should consult cs    -rv *)
  (* No other cases can occur due to whnf invariant *)
  (* collectExp (tag_, d, G, (U, s), K) = K'

       same as collectExpW  but  (U,s) need not to be in whnf
    *)
  (* collectSpine (tag_, d, G, (S, s), K) = K'

       Invariant:
       If    G |- s : G1     G1 |- S : V > P
       then  K' = K, K''
       where K'' contains all EVars and BVars in (S, s)
     *)
  (* collectDec (tag_, d, G, (x:V, s), K) = K'

       Invariant:
       If    G |- s : G1     G1 |- V : L
       then  K' = K, K''
       where K'' contains all EVars and BVars in (V, s)
    *)
  (* collectSub (tag_, d, G, s, K) = K'

       Invariant:
       If    G |- s : G1
       then  K' = K, K''
       where K'' contains all EVars and BVars in s
    *)
  (* abstractEVar (K, depth, X) = C'

       Invariant:
       If   G |- X : V
       and  |G| = depth
       and  X occurs in K  at kth position (starting at 1)
       then C' = BVar (depth + k)
       and  {{K}}, G |- C' : V
    *)
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
  (* abstractExpW (K, depth, (U, s)) = U'
       U' = {{U[s]}}_K

       Invariant:
       If    G |- s : G1     G1 |- U : V    (U,s) is in whnf
       and   K is internal context in dependency order
       and   |G| = depth
       and   K ||- U and K ||- V
       then  {{K}}, G |- U' : V'
       and   . ||- U' and . ||- V'
       and   U' is in nf
    *)
  (* s = id *)
  (* hack - should consult cs   -rv *)
  (* abstractExp (K, depth, (U, s)) = U'

       same as abstractExpW, but (U,s) need not to be in whnf
    *)
  (* abstractSub (K, depth, s, S) = S'      (implicit raising)
       S' = {{s}}_K @@ S

       Invariant:
       If   G |- s : G1
       and  |G| = depth
       and  K ||- s
       then {{K}}, G |- S' : {G1}.W > W   (for some W)
       and  . ||- S'
    *)
  (* n = 0 *)
  (* abstractSpine (K, depth, (S, s)) = S'
       where S' = {{S[s]}}_K

       Invariant:
       If   G |- s : G1     G1 |- S : V > P
       and  K ||- S
       and  |G| = depth

       then {{K}}, G |- S' : V' > P'
       and  . ||- S'
    *)
  (* abstractDec (K, depth, (x:V, s)) = x:V'
       where V = {{V[s]}}_K

       Invariant:
       If   G |- s : G1     G1 |- V : L
       and  K ||- V
       and  |G| = depth

       then {{K}}, G |- V' : L
       and  . ||- V'
    *)
  (* getlevel (V) = L if G |- V : L

       Invariant: G |- V : L' for some L'
    *)
  (* checkType (V) = () if G |- V : type

       Invariant: G |- V : L' for some L'
    *)
  (* abstractCtx (K, V) = V'
       where V' = {{K}} V

       Invariant:
       If   {{K}} |- V : L
       and  . ||- V

       then V' = {{K}} V
       and  . |- V' : L
       and  . ||- V'
    *)
  (* abstractGlobalSub (K, s, B) = s'

       Invariant:
       If   K > G   aux context
       and  G |- s : G'
       then K |- s' : G'
    *)
  (* collectGlobalSub (G0, s, B, collect) = collect'

       Invariant:
       If   |- G0 ctx
       and  |- G ctx
       and  G |- B tags
       and  G0 |- s : G
       and  collect is a function which maps
               (d, K)  (d expresses the number of parameters in K, |- K aux ctx)
            to K'      (|- K' aux ctx, which collects all EVars in K)
    *)
  (* no cases for (G0, s, B as I.Decl (_, S.Parameter NONE), collect) *)
  (* abstractNew ((G0, B0), s, B) = ((G', B'), s')

       Invariant:
       If   . |- G0 ctx
       and  G0 |- B0 tags
       and  G0 |- s : G
       and  G |- B tags
       then . |- G' = G1, Gp, G2
       and  G' |- B' tags
       and  G' |- s' : G
    *)
  (* abstractSub (t, B1, (G0, B0), s, B) = ((G', B'), s')

       Invariant:
       If   . |- t : G1
       and  G1 |- B1 tags

       and  G0 |- B0 tags
       and  G0 |- s : G
       and  G |- B tags
       then . |- G' = G1, G0, G2
       and  B' |- G' tags
       and  G' |- s' : G
    *)
  (* skip'' (K, (G, B)) = K'

             Invariant:
             If   G = x1:V1 .. xn:Vn
             and  G |- B = <param> ... <param> tags
             then  K' = K, BV (x1) .. BV (xn)
          *)
  (* abstractFor (K, depth, (F, s)) = F'
       F' = {{F[s]}}_K

       Invariant:
       If    G |- s : G1     G1 |- U : V    (U,s) is in whnf
       and   K is internal context in dependency order
       and   |G| = depth
       and   K ||- U and K ||- V
       then  {{K}}, G |- U' : V'
       and   . ||- U' and . ||- V'
       and   U' is in nf
    *)
  (* abstract (Gx, F) = F'

       Invariant:
       If   G, Gx |- F formula
       then G |- F' = {{Gx}} F formula
    *)
  (* shift G = s'

       Invariant:
       Forall contexts G0:
       If   |- G0, G ctx
       then G0, V, G |- s' : G0, G
    *)
  (* ctxSub (G, s) = G'

       Invariant:
       If   G2 |- s : G1
       and  G1 |- G ctx
       then G2 |- G' = G[s] ctx
    *)
  (* weaken2 (G, a, i, S) = w'

       Invariant:
       G |- w' : Gw
       Gw < G
       G |- S : {Gw} V > V
    *)
  (* raiseType (G, V) = {{G}} V

       Invariant:
       If G |- V : L
       then  . |- {{G}} V : L

       All abstractions are potentially dependent.
    *)
  (* raiseFor (G, F, w, sc) = F'

       Invariant:
       If   G0 |- G ctx
       and  G0, G, GF |- F for
       and  G0, {G} GF [...] |- w : G0
       and  sc maps  (G0, GA |- w : G0, |GA|)  to   (G0, GA, G[..] |- s : G0, G, GF)
       then G0, {G} GF |- F' for
    *)
  (* G0, {G}GF[..], G |- s : G0, G, GF *)
  (* G0, {G}GF[..], G |- V' : type *)
  (* G0, {G}GF[..], G |- nw : G0, {G}GF[..], Gw
                                         Gw < G *)
  (* G0, {G}GF[..], Gw |- iw : G0, {G}GF[..], G *)
  (* Generalize the invariant for Whnf.strengthen --cs *)
  (* G0, {G}GF[..], Gw |- V'' = V'[iw] : type*)
  (* G0, {G}GF[..] |- V''' = {Gw} V'' : type*)
  (* G0, {G}GF[..], G[..] |- S''' : {Gw} V''[..] > V''[..] *)
  (* G0, {G}GF[..], G |- s : G0, G, GF *)
  (* G0, GA |- w' : G0 *)
  (* G0, GA, G[..] |- s' : G0, G, GF *)
  (* G0, GA, G[..] |- (g+k'-k). S', s' : G0, G, GF, V *)
  (*                val G = F.listToCtx (ctxSub (F.ctxToList Gorig, w))
                  val g = I.ctxLength G
                  val s = sc (w, k)
                                         G0, {G}GF[..], G |- s : G0, G, GF 
                  val V' = Whnf.normalize (raiseType (G, Whnf.normalize (V, s)), I.id)
                                         G0, {G}GF[..] |- V' = {G}(V[s]) : type 
                  val S' = spine g
                                         G0, {G}GF[..] |- S' > {G}(V[s]) > V[s] 
                  val sc' = fn (w', k') =>
                              let
                                         G0, GA |- w' : G0 
                                val s' = sc (w', k')
                                         G0, GA, G[..] |- s' : G0, G, GF 
                              in
                                I.Dot (I.Exp (I.Root (I.BVar (g + k'-k), S')), s')
                                         G0, GA, G[..] |- g+k'-k. S', s' : G0, G, GF, V 
                              end
                  val F' = raiseFor (k+1, Gorig, F, I.comp (w, I.shift), sc')
                in
                  F.All (F.Prim (I.Dec (name, V')), F')
*)
  (* G0, {G}GF[..], G |- s : G0, G, GF *)
  (* G0, {G}GF[..], G |- V' : type *)
  (* G0, {G}GF[..], G |- nw : G0, {G}GF[..], Gw
                                         Gw < G *)
  (* G0, {G}GF[..], Gw |- iw : G0, {G}GF[..], G *)
  (* Generalize the invariant for Whnf.strengthen --cs *)
  (* G0, {G}GF[..], Gw |- V'' = V'[iw] : type*)
  (* G0, {G}GF[..] |- V''' = {Gw} V'' : type*)
  (* G0, {G}GF[..], G[..] |- S''' : {Gw} V''[..] > V''[..] *)
  (* G0, {G}GF[..], G |- s : G0, G, GF *)
  (* G0, GA |- w' : G0 *)
  (* G0, GA, G[..] |- s' : G0, G, GF *)
  (* G0, GA, G[..] |- (g+k'-k). S', s' : G0, G, GF, V *)
  (* the other case of F.All (F.Block _, _) is not yet covered *)
  (* makeFor (G, w, AF) = F'

       Invariant :
       If   |- G ctx
       and  G |- w : G'
       and  G' |- AF approx for
       then G'; . |- F' = {EVARS} AF  for
    *)
  (*        val _ = if !Global.doubleCheck then checkTags (GK, BK) else () *)
  (* BUG *)
  let weaken = weaken
  let raiseType = raiseType
  let abstractSub = abstractSubAll
  let abstractSub' a1 a2 b c = abstractNew ((a1, a2), b, c)
  let abstractApproxFor = abstractApproxFor
end
(*! sharing Abstract.IntSyn = IntSyn' !*)
(* functor MTPAbstract *)

(* # 1 "src/meta/MtpAbstract.sml.ml" *)
