
(* # 1 "src/lambda/Abstract.sig.ml" *)
open Intsyn_
open Tomega

(* Abstraction *)
(* Author: Frank Pfenning, Carsten Schuermann *)
include ABSTRACT
(* signature ABSTRACT *)

(* # 1 "src/lambda/Abstract.fun.ml" *)
open! Whnf
open! Unify
open! Constraints
open! Basis
open Intsyn_
open Tomega

(* Abstraction *)
(* Author: Frank Pfenning, Carsten Schuermann *)
(* Modified: Roberto Virga *)
exception Error of string

let () =
  Printexc.register_printer (function Error msg -> Some msg | _ -> None)

module MakeAbstract (Whnf : WHNF) (Unify : UNIFY) (Constraints : CONSTRAINTS) :
  ABSTRACT = struct
  exception Error = Error

  open! struct
    module I = IntSyn
    module T = Tomega
    module C = Constraints
    module O = Order

    type eFLVar =
      | Ev of I.exp
      | Fv of string * I.exp
      | Lv of I.block
      | Pv of T.prg

    let rec collectConstraints = function
      | I.Null -> []
      | I.Decl (g, Fv _) -> collectConstraints g
      | I.Decl (g, Ev (I.EVar (_, _, _, { contents = [] }))) ->
          collectConstraints g
      | I.Decl (g, Ev (I.EVar (_, _, _, { contents = cnstrL }))) ->
          C.simplify cnstrL @ collectConstraints g
      | I.Decl (g, Lv _) -> collectConstraints g

    let checkConstraints k =
      let constraints = collectConstraints k in
      ignore begin match constraints with
        | [] -> ()
        | _ -> raise (C.Error constraints)
        end;
      ()

    let eqEVar arg__1 arg__2 =
      begin match (arg__1, arg__2) with
      | I.EVar (r1, _, _, _), Ev (I.EVar (r2, _, _, _)) -> r1 == r2
      | _, _ -> false
      end

    let eqFVar arg__3 arg__4 =
      begin match (arg__3, arg__4) with
      | I.FVar (n1, _, _), Fv (n2, _) -> n1 = n2
      | _, _ -> false
      end

    let eqLVar arg__5 arg__6 =
      begin match (arg__5, arg__6) with
      | I.LVar (r1, _, _), Lv (I.LVar (r2, _, _)) -> r1 == r2
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
      | I.FgnExp (csfe_csid, csfe_ops) ->
          I.FgnExpStd.fold csfe_csid csfe_ops
            (function
              | u, dp ->
                  ( or ) (dp, occursInExp (k, Whnf.normalize (u, I.id))))
            I.No

    and occursInHead (k, a, dp) = match a, dp with
      | I.BVar k', dp ->
          begin if k = k' then I.Maybe else dp
          end
      | I.Const _, dp -> dp
      | I.Def _, dp -> dp
      | I.Proj _, dp -> dp
      | I.FgnConst _, dp -> dp
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

    let rec raiseType a1 b1 = match a1, b1 with
      | I.Null, v -> v
      | I.Decl (g, d), v -> raiseType g (I.Pi ((d, I.Maybe), v))

    let rec raiseTerm a1 b1 = match a1, b1 with
      | I.Null, u -> u
      | I.Decl (g, d), u -> raiseTerm g (I.Lam (d, u))

    let rec collectExpW (g, a, k) = match a with
      | (I.Uni l, s) -> k
      | (I.Pi ((d, _), v), s) ->
          collectExp
            ( I.Decl (g, I.decSub d s),
              (v, I.dot1 s),
              collectDec (g, (d, s), k) )
      | (I.Root ((I.FVar (name, v, s') as f), s_), s) ->
          begin if exists (eqFVar f) k then collectSpine (g, (s_, s), k)
          else
            collectSpine
              ( g,
                (s_, s),
                I.Decl (collectExp (I.Null, (v, I.id), k), Fv (name, v)) )
          end
      | ( I.Root
              (I.Proj ((I.LVar ({ contents = None }, sk, (l, t)) as l_), i), s_),
            s ) ->
          collectSpine (g, (s_, s), collectBlock (g, I.blockSub l_ s, k))
      | (I.Root (_, s_), s) -> collectSpine (g, (s_, s), k)
      | (I.Lam (d, u), s) ->
          collectExp
            ( I.Decl (g, I.decSub d s),
              (u, I.dot1 s),
              collectDec (g, (d, s), k) )
      | ((I.EVar (r, gx, v, cnstrs) as x), s) ->
          begin if exists (eqEVar x) k then collectSub (g, s, k)
          else
            let v' = raiseType gx v in
            let k' = collectExp (I.Null, (v', I.id), k) in
            collectSub (g, s, I.Decl (k', Ev x))
          end
      | (I.FgnExp (csfe_csid, csfe_ops), s) ->
          I.FgnExpStd.fold csfe_csid csfe_ops
            (function u, k -> collectExp (g, (u, s), k))
            k

    and collectExp (g, us, k) = collectExpW (g, Whnf.whnf us, k)

    and collectSpine (g, a, k) = match a with
      | (I.Nil, _) -> k
      | (I.SClo (s_, s'), s) ->
          collectSpine (g, (s_, I.comp s' s), k)
      | (I.App (u, s_), s) ->
          collectSpine (g, (s_, s), collectExp (g, (u, s), k))

    and collectDec (g, a, k) = match a with
      | (I.Dec (_, v), s) -> collectExp (g, (v, s), k)
      | (I.BDec (_, (_, t)), s) -> collectSub (g, I.comp t s, k)
      | (I.NDec _, s) -> k

    and collectSub (g, a, k) = match a with
      | I.Shift _ -> k
      | I.Dot (I.Idx _, s) -> collectSub (g, s, k)
      | I.Dot (I.Exp u, s) ->
          collectSub (g, s, collectExp (g, (u, I.id), k))
      | I.Dot (I.Block b, s) ->
          collectSub (g, s, collectBlock (g, b, k))

    and collectBlock (g, a, k) = match a with
      | I.LVar ({ contents = Some b }, sk, _) ->
          collectBlock (g, I.blockSub b sk, k)
      | (I.LVar (_, sk, (l, t)) as l_) ->
          begin if exists (eqLVar l_) k then collectSub (g, I.comp t sk, k)
          else I.Decl (collectSub (g, I.comp t sk, k), Lv l_)
          end

    let rec collectCtx (g0, a, k) = match a with
      | I.Null -> (g0, k)
      | I.Decl (g, d) ->
          let g0', k' = collectCtx (g0, g, k) in
          let k'' = collectDec (g0', (d, I.id), k') in
          (I.Decl (g0, d), k'')

    let rec collectCtxs (g0, a, k) = match a with
      | [] -> k
      | g :: gs ->
          let g0', k' = collectCtx (g0, g, k) in
          collectCtxs (g0', gs, k')

    let rec abstractEVar (a, depth, b) = match a, b with
      | I.Decl (k', Ev (I.EVar (r', _, _, _))), (I.EVar (r, _, _, _) as x) ->
          begin if r == r' then I.BVar (depth + 1)
          else abstractEVar (k', depth + 1, x)
          end
      | I.Decl (k', _), x -> abstractEVar (k', depth + 1, x)

    let rec abstractFVar (a, depth, b) = match a, b with
      | I.Decl (k', Fv (n', _)), (I.FVar (n, _, _) as f) ->
          begin if n = n' then I.BVar (depth + 1)
          else abstractFVar (k', depth + 1, f)
          end
      | I.Decl (k', _), f -> abstractFVar (k', depth + 1, f)

    let rec abstractLVar (a, depth, b) = match a, b with
      | I.Decl (k', Lv (I.LVar (r', _, _))), (I.LVar (r, _, _) as l) ->
          begin if r == r' then I.Bidx (depth + 1)
          else abstractLVar (k', depth + 1, l)
          end
      | I.Decl (k', _), l -> abstractLVar (k', depth + 1, l)

    let rec abstractExpW (k, depth, a) = match a with
      | ((I.Uni l as u), s) -> u
      | (I.Pi ((d, p), v), s) ->
          piDepend
            (abstractDec (k, depth, (d, s))) p (abstractExp (k, depth + 1, (v, I.dot1 s)))
      | (I.Root ((I.FVar _ as f), s_), s) ->
          I.Root
            (abstractFVar (k, depth, f), abstractSpine (k, depth, (s_, s)))
      | (I.Root (I.Proj ((I.LVar _ as l), i), s_), s) ->
          I.Root
            ( I.Proj (abstractLVar (k, depth, l), i),
              abstractSpine (k, depth, (s_, s)) )
      | (I.Root (h, s_), s) ->
          I.Root (h, abstractSpine (k, depth, (s_, s)))
      | (I.Lam (d, u), s) ->
          I.Lam
            ( abstractDec (k, depth, (d, s)),
              abstractExp (k, depth + 1, (u, I.dot1 s)) )
      | ((I.EVar _ as x), s) ->
          I.Root
            (abstractEVar (k, depth, x), abstractSub (k, depth, s, I.Nil))
      | (I.FgnExp (csfe_csid, csfe_ops), s) ->
          I.FgnExpStd.Map.apply csfe_csid csfe_ops (function u ->
              abstractExp (k, depth, (u, s)))

    and abstractExp (k, depth, us) = abstractExpW (k, depth, Whnf.whnf us)

    and abstractSub (k_, depth, a, s_) = match a with
      | I.Shift k ->
          begin if k < depth then
            abstractSub (k_, depth, I.Dot (I.Idx (k + 1), I.Shift (k + 1)), s_)
          else s_
          end
      | I.Dot (I.Idx k, s) ->
          abstractSub (k_, depth, s, I.App (I.Root (I.BVar k, I.Nil), s_))
      | I.Dot (I.Exp u, s) ->
          abstractSub
            (k_, depth, s, I.App (abstractExp (k_, depth, (u, I.id)), s_))

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

    let rec abstractSOME (k_, a) = match a with
      | I.Shift 0 -> I.Shift (I.ctxLength k_)
      | I.Shift n -> I.Shift (I.ctxLength k_)
      | I.Dot (I.Idx k, s) -> I.Dot (I.Idx k, abstractSOME (k_, s))
      | I.Dot (I.Exp u, s) ->
          I.Dot (I.Exp (abstractExp (k_, 0, (u, I.id))), abstractSOME (k_, s))
      | I.Dot (I.Block (I.LVar _ as l), s) ->
          I.Dot (I.Block (abstractLVar (k_, 0, l)), abstractSOME (k_, s))

    let rec abstractCtx (k, depth, a) = match a with
      | I.Null -> (I.Null, depth)
      | I.Decl (g, d) ->
          let g', depth' = abstractCtx (k, depth, g) in
          let d' = abstractDec (k, depth', (d, I.id)) in
          (I.Decl (g', d'), depth' + 1)

    let rec abstractCtxlist (k, depth, a) = match a with
      | [] -> []
      | g :: gs ->
          let g', depth' = abstractCtx (k, depth, g) in
          let gs' = abstractCtxlist (k, depth', gs) in
          g' :: gs'

    let rec abstractKPi (a, v) = match a with
      | I.Null -> v
      | I.Decl (k', Ev (I.EVar (_, gx, vx, _))) ->
          let v' = raiseType gx vx in
          let v'' = abstractExp (k', 0, (v', I.id)) in
          abstractKPi (k', I.Pi ((I.Dec (None, v''), I.Maybe), v))
      | I.Decl (k', Fv (name, v')) ->
          let v'' = abstractExp (k', 0, (v', I.id)) in
          abstractKPi (k', I.Pi ((I.Dec (Some name, v''), I.Maybe), v))
      | I.Decl (k', Lv (I.LVar (r, _, (l, t)))) ->
          let t' = abstractSOME (k', t) in
          abstractKPi (k', I.Pi ((I.BDec (None, (l, t')), I.Maybe), v))

    let rec abstractKLam (a, u) = match a with
      | I.Null -> u
      | I.Decl (k', Ev (I.EVar (_, gx, vx, _))) ->
          let v' = raiseType gx vx in
          abstractKLam
            (k', I.Lam (I.Dec (None, abstractExp (k', 0, (v', I.id))), u))
      | I.Decl (k', Fv (name, v')) ->
          abstractKLam
            ( k',
              I.Lam (I.Dec (Some name, abstractExp (k', 0, (v', I.id))), u)
            )

    let rec abstractKCtx = function
      | I.Null -> I.Null
      | I.Decl (k', Ev (I.EVar (_, gx, vx, _))) ->
          let v' = raiseType gx vx in
          let v'' = abstractExp (k', 0, (v', I.id)) in
          I.Decl (abstractKCtx k', I.Dec (None, v''))
      | I.Decl (k', Fv (name, v')) ->
          let v'' = abstractExp (k', 0, (v', I.id)) in
          I.Decl (abstractKCtx k', I.Dec (Some name, v''))
      | I.Decl (k', Lv (I.LVar (r, _, (l, t)))) ->
          let t' = abstractSOME (k', t) in
          I.Decl (abstractKCtx k', I.BDec (None, (l, t')))

    let abstractDecImp v =
      let k = collectExp (I.Null, (v, I.id), I.Null) in
      ignore (checkConstraints k);
      (I.ctxLength k, abstractKPi (k, abstractExp (k, 0, (v, I.id))))

    let abstractDef u v =
      let k =
        collectExp (I.Null, (u, I.id), collectExp (I.Null, (v, I.id), I.Null))
      in
      ignore (checkConstraints k);
      ( I.ctxLength k,
        ( abstractKLam (k, abstractExp (k, 0, (u, I.id))),
          abstractKPi (k, abstractExp (k, 0, (v, I.id))) ) )

    let abstractSpineExt (s_, s) =
      let k = collectSpine (I.Null, (s_, s), I.Null) in
      ignore (checkConstraints k);
      let g = abstractKCtx k in
      let s_ = abstractSpine (k, 0, (s_, s)) in
      (g, s_)

    let abstractCtxs gs =
      let k = collectCtxs (I.Null, gs, I.Null) in
      ignore (checkConstraints k);
      (abstractKCtx k, abstractCtxlist (k, 0, gs))

    let closedDec g (I.Dec (_, v), s) =
      begin match collectExp (g, (v, s), I.Null) with
      | I.Null -> true
      | _ -> false
      end

    let rec closedSub a1 b1 = match a1, b1 with
      | g, I.Shift _ -> true
      | g, I.Dot (I.Idx _, s) -> closedSub g s
      | g, I.Dot (I.Exp u, s) ->
          begin match collectExp (g, (u, I.id), I.Null) with
          | I.Null -> closedSub g s
          | _ -> false
          end

    let closedExp g (u, s) =
      begin match collectExp (g, (u, I.id), I.Null) with
      | I.Null -> true
      | _ -> false
      end

    let rec closedCtx = function
      | I.Null -> true
      | I.Decl (g, d) -> closedCtx g && closedDec g (d, I.id)

    let rec closedFor (psi, a) = match a with
      | True -> true
      | T.All ((d, _), f) ->
          closedDEC (psi, d) && closedFor (I.Decl (psi, d), f)
      | T.Ex ((d, _), f) ->
          closedDec (T.coerceCtx psi) (d, I.id)
          && closedFor (I.Decl (psi, T.UDec d), f)

    and closedDEC (psi, a) = match a with
      | T.UDec d -> closedDec (T.coerceCtx psi) (d, I.id)
      | T.PDec (_, f, _, _) -> closedFor (psi, f)

    let rec closedCTX = function
      | I.Null -> true
      | I.Decl (psi, d) -> closedCTX psi && closedDEC (psi, d)

    let rec evarsToK = function
      | [] -> I.Null
      | x :: xs -> I.Decl (evarsToK xs, Ev x)

    let rec kToEVars = function
      | I.Null -> []
      | I.Decl (k, Ev x) -> x :: kToEVars k
      | I.Decl (k, _) -> kToEVars k

    let collectEVars g us xs =
      kToEVars (collectExp (g, us, evarsToK xs))

    let collectEVarsSpine g (s_, s) xs =
      kToEVars (collectSpine (g, (s_, s), evarsToK xs))

    let rec collectPrg (a, b, k) = match a, b with
      | _, (T.EVar (psi, r, f, _, _, _) as p) -> I.Decl (k, Pv p)
      | psi, Unit -> k
      | psi, T.PairExp (u, p) ->
          collectPrg (psi, p, collectExp (T.coerceCtx psi, (u, I.id), k))

    let rec abstractPVar (a, depth, b) = match a, b with
      | I.Decl (k', Pv (T.EVar (_, r', _, _, _, _))), (T.EVar (_, r, _, _, _, _) as p) ->
          begin if r == r' then T.Var (depth + 1)
          else abstractPVar (k', depth + 1, p)
          end
      | I.Decl (k', _), p -> abstractPVar (k', depth + 1, p)

    let rec abstractPrg (k, depth, a) = match a with
      | (T.EVar _ as x) -> abstractPVar (k, depth, x)
      | T.Unit -> T.Unit
      | T.PairExp (u, p) ->
          T.PairExp
            (abstractExp (k, depth, (u, I.id)), abstractPrg (k, depth, p))

    let rec collectTomegaSub = function
      | T.Shift 0 -> I.Null
      | T.Dot (T.Exp u, t) ->
          collectExp (I.Null, (u, I.id), collectTomegaSub t)
      | T.Dot (T.Block b, t) -> collectBlock (I.Null, b, collectTomegaSub t)
      | T.Dot (T.Prg p, t) -> collectPrg (I.Null, p, collectTomegaSub t)

    let rec abstractOrder (k, depth, a) = match a with
      | O.Arg (us1, us2) ->
          O.Arg
            ( (abstractExp (k, depth, us1), I.id),
              (abstractExp (k, depth, us2), I.id) )
      | O.Simul os ->
          O.Simul (map (function o -> abstractOrder (k, depth, o)) os)
      | O.Lex os ->
          O.Lex (map (function o -> abstractOrder (k, depth, o)) os)

    let rec abstractTC (k, depth, a) = match a with
      | T.Abs (d, tc) ->
          T.Abs (abstractDec (k, depth, (d, I.id)), abstractTC (k, depth, tc))
      | T.Conj (tc1, tc2) ->
          T.Conj (abstractTC (k, depth, tc1), abstractTC (k, depth, tc2))
      | T.Base o -> T.Base (abstractOrder (k, depth, o))

    let abstractTCOpt (k, depth, a) = match a with
      | None -> None
      | Some tc -> Some (abstractTC (k, depth, tc))

    let rec abstractMetaDec (k, depth, a) = match a with
      | T.UDec d -> T.UDec (abstractDec (k, depth, (d, I.id)))
      | T.PDec (xx, f, tc1, tc2) ->
          T.PDec (xx, abstractFor (k, depth, f), tc1, tc2)

    and abstractFor (k, depth, a) = match a with
      | T.True -> T.True
      | T.All ((md, q), f) ->
          T.All
            ((abstractMetaDec (k, depth, md), q), abstractFor (k, depth, f))
      | T.Ex ((d, q), f) ->
          T.Ex
            ( (abstractDec (k, depth, (d, I.id)), q),
              abstractFor (k, depth, f) )
      | T.And (f1, f2) ->
          T.And (abstractFor (k, depth, f1), abstractFor (k, depth, f2))
      | T.World (w, f) -> T.World (w, abstractFor (k, depth, f))

    let rec abstractPsi = function
      | I.Null -> I.Null
      | I.Decl (k', Ev (I.EVar (_, gx, vx, _))) ->
          let v' = raiseType gx vx in
          let v'' = abstractExp (k', 0, (v', I.id)) in
          I.Decl (abstractPsi k', T.UDec (I.Dec (None, v'')))
      | I.Decl (k', Fv (name, v')) ->
          let v'' = abstractExp (k', 0, (v', I.id)) in
          I.Decl (abstractPsi k', T.UDec (I.Dec (Some name, v'')))
      | I.Decl (k', Lv (I.LVar (r, _, (l, t)))) ->
          let t' = abstractSOME (k', t) in
          I.Decl (abstractPsi k', T.UDec (I.BDec (None, (l, t'))))
      | I.Decl (k', Pv (T.EVar (gx, _, fx, tc1, tc2, _))) ->
          let f' = abstractFor (k', 0, T.forSub fx T.id) in
          let tc1' = abstractTCOpt (k', 0, tc1) in
          let tc2' = abstractTCOpt (k', 0, tc2) in
          I.Decl (abstractPsi k', T.PDec (None, f', tc1, tc2))

    let rec abstractTomegaSub t =
      let k = collectTomegaSub t in
      let t' = abstractTomegaSub' (k, 0, t) in
      let psi = abstractPsi k in
      (psi, t')

    and abstractTomegaSub' (k, depth, a) = match a with
      | T.Shift 0 -> T.Shift depth
      | T.Dot (T.Exp u, t) ->
          T.Dot
            ( T.Exp (abstractExp (k, depth, (u, I.id))),
              abstractTomegaSub' (k, depth, t) )
      | T.Dot (T.Block b, t) ->
          T.Dot
            ( T.Block (abstractLVar (k, depth, b)),
              abstractTomegaSub' (k, depth, t) )
      | T.Dot (T.Prg p, t) ->
          T.Dot
            ( T.Prg (abstractPrg (k, depth, p)),
              abstractTomegaSub' (k, depth, t) )

    let abstractTomegaPrg p =
      let k = collectPrg (I.Null, p, I.Null) in
      let p' = abstractPrg (k, 0, p) in
      let psi = abstractPsi k in
      (psi, p')
  end

  (* Intermediate Data Structure *)
  (* Y ::= X         for  GX |- X : VX *)
  (*     | (F, V)        if . |- F : V *)
  (*     | L             if . |- L in W *)
  (*     | P                            *)
  (*
       We write {{K}} for the context of K, where EVars, FVars, LVars have
       been translated to declarations and their occurrences to BVars.
       We write {{U}}_K, {{S}}_K for the corresponding translation of an
       expression or spine.

       Just like contexts G, any K is implicitly assumed to be
       well-formed and in dependency Order.

       We write  K ||- U  if all EVars and FVars in U are collected in K.
       In particular, . ||- U means U contains no EVars or FVars.  Similarly,
       for spines K ||- S and other syntactic categories.

       Collection and abstraction raise Error if there are unresolved
       constraints after simplification.
    *)
  (* collectConstraints K = cnstrs
       where cnstrs collects all constraints attached to EVars in K
    *)
  (* checkConstraints (K) = ()
       Effect: raises Constraints.Error(C) if K contains unresolved constraints
    *)
  (* checkEmpty Cnstr = ()
       raises Error exception if constraints Cnstr cannot be simplified
       to the empty constraint
    *)
  (*
    fun checkEmpty (nil) = ()
      | checkEmpty (Cnstr) =
        (case C.simplify Cnstr
           of nil => ()
            | _ => raise Error ""Typing ambiguous -- unresolved constraints"")
    *)
  (* eqEVar X Y = B
       where B iff X and Y represent same variable
    *)
  (* eqFVar F Y = B
       where B iff X and Y represent same variable
    *)
  (* eqLVar L Y = B
       where B iff X and Y represent same variable
    *)
  (* exists P K = B
       where B iff K = K1, Y, K2  s.t. P Y  holds
    *)
  (* this should be non-strict *)
  (* perhaps the whole repeated traversal are now a performance
       bottleneck in PCC applications where logic programming search
       followed by abstraction creates certificates.  such certificates
       are large, so the quadratic algorithm is not really acceptable.
       possible improvement, collect, abstract, then traverse one more
       time to determine status of all variables.
    *)
  (* Wed Aug  6 16:37:57 2003 -fp *)
  (* !!! *)
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
  (* raiseType (G, V) = {{G}} V

       Invariant:
       If G |- V : L
       then  . |- {{G}} V : L

       All abstractions are potentially dependent.
    *)
  (* raiseTerm (G, U) = [[G]] U

       Invariant:
       If G |- U : V
       then  . |- [[G]] U : {{G}} V

       All abstractions are potentially dependent.
    *)
  (* collectExpW (G, (U, s), K) = K'

       Invariant:
       If    G |- s : G1     G1 |- U : V      (U,s) in whnf
       No circularities in U
             (enforced by extended occurs-check for FVars in Unify)
       and   K' = K, K''
             where K'' contains all EVars and FVars in (U,s)
    *)
  (* Possible optimization: Calculate also the normal form of the term *)
  (* s' = ^|G| *)
  (* BUG : We forget to deref L.  use collectBlock instead
             FPCHECK
             -cs Sat Jul 24 18:48:59 2010
            was:
      | collectExpW (G, (I.Root (I.Proj (L as I.LVar (r, sk, (l, t)), i), S), s), K) =
        if exists (eqLVar L) K
           note: don't collect t again below 
           was: collectSpine (G, (S, s), collectSub (I.Null, t, K)) 
           Sun Dec 16 10:54:52 2001 -fp !!! 
          then collectSpine (G, (S, s), K)
        else
           -fp Sun Dec  1 21:12:12 2002 
         collectSpine (G, (S, s), I.Decl (collectSub (G, I.comp(t,s), K), LV L)) 
         was :
         collectSpine (G, (S, s), collectSub (G, I.comp(t,s), I.Decl (K, LV L)))
         July 22, 2010 -fp -cs
         
            collectSpine (G, (S, s), collectSub (G, I.comp(t,I.comp(sk,s)),
                                                 I.Decl (K, LV L)))
*)
  (* val _ = checkEmpty !cnstrs *)
  (* inefficient *)
  (* No other cases can occur due to whnf invariant *)
  (* collectExp (G, (U, s), K) = K'

       same as collectExpW  but  (U,s) need not to be in whnf
    *)
  (* collectSpine (G, (S, s), K) = K'

       Invariant:
       If    G |- s : G1     G1 |- S : V > P
       then  K' = K, K''
       where K'' contains all EVars and FVars in (S, s)
     *)
  (* collectDec (G, (x:V, s), K) = K'

       Invariant:
       If    G |- s : G1     G1 |- V : L
       then  K' = K, K''
       where K'' contains all EVars and FVars in (V, s)
    *)
  (* . |- t : Gsome, so do not compose with s *)
  (* Sat Dec  8 13:28:15 2001 -fp *)
  (* was: collectSub (I.Null, t, K) *)
  (* collectSub (G, s, K) = K'

       Invariant:
       If    G |- s : G1
       then  K' = K, K''
       where K'' contains all EVars and FVars in s
    *)
  (* next case should be impossible *)
  (*
      | collectSub (G, I.Dot (I.Undef, s), K) =
          collectSub (G, s, K)
    *)
  (* collectBlock (G, B, K) where G |- B block *)
  (* collectBlock (B, K) *)
  (* correct?? -fp Sun Dec  1 21:15:33 2002 *)
  (* was: t in the two lines above, July 22, 2010, -fp -cs *)
  (* | collectBlock (G, I.Bidx _, K) = K *)
  (* should be impossible: Fronts of substitutions are never Bidx *)
  (* Sat Dec  8 13:30:43 2001 -fp *)
  (* collectCtx (G0, G, K) = (G0', K')
       Invariant:
       If G0 |- G ctx,
       then G0' = G0,G
       and K' = K, K'' where K'' contains all EVars and FVars in G
    *)
  (* collectCtxs (G0, Gs, K) = K'
       Invariant: G0 |- G1,...,Gn ctx where Gs = [G1,...,Gn]
       and K' = K, K'' where K'' contains all EVars and FVars in G1,...,Gn
    *)
  (* abstractEVar (K, depth, X) = C'

       Invariant:
       If   G |- X : V
       and  |G| = depth
       and  X occurs in K  at kth position (starting at 1)
       then C' = BVar (depth + k)
       and  {{K}}, G |- C' : V
    *)
  (*      | abstractEVar (I.Decl (K', FV (n', _)), depth, X) =
          abstractEVar (K', depth+1, X) remove later --cs*)
  (* abstractFVar (K, depth, F) = C'

       Invariant:
       If   G |- F : V
       and  |G| = depth
       and  F occurs in K  at kth position (starting at 1)
       then C' = BVar (depth + k)
       and  {{K}}, G |- C' : V
    *)
  (*      | abstractFVar (I.Decl(K', EV _), depth, F) =
          abstractFVar (K', depth+1, F) remove later --cs *)
  (* abstractLVar (K, depth, L) = C'

       Invariant:
       If   G |- L : V
       and  |G| = depth
       and  L occurs in K  at kth position (starting at 1)
       then C' = Bidx (depth + k)
       and  {{K}}, G |- C' : V
    *)
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
  (* k = depth *)
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
  (* abstractSOME (K, s) = s'
       s' = {{s}}_K

       Invariant:
       If    . |- s : Gsome
       and   K is internal context in dependency order
       and   K ||- s
       then  {{K}} |- s' : Gsome  --- not changing domain of s'

       Update: modified for globality invariant of . |- t : Gsome
       Sat Dec  8 13:35:55 2001 -fp
       Above is now incorrect
       Sun Dec  1 22:36:50 2002 -fp
    *)
  (* n = 0 by invariant, check for now *)
  (* n > 0 *)
  (* I.Block (I.Bidx _) should be impossible as head of substitutions *)
  (* abstractCtx (K, depth, G) = (G', depth')
       where G' = {{G}}_K

       Invariants:
       If G0 |- G ctx
       and K ||- G
       and |G0| = depth
       then {{K}}, G0 |- G' ctx
       and . ||- G'
       and |G0,G| = depth'
    *)
  (* abstractCtxlist (K, depth, [G1,...,Gn]) = [G1',...,Gn']
       where Gi' = {{Gi}}_K

       Invariants:
       if G0 |- G1,...,Gn ctx
       and K ||- G1,...,Gn
       and |G0| = depth
       then {{K}}, G0 |- G1',...,Gn' ctx
       and . ||- G1',...,Gn'
    *)
  (* dead code under new reconstruction -kw
     getlevel (V) = L if G |- V : L

       Invariant: G |- V : L' for some L'
    
    fun getLevel (I.Uni _) = I.Kind
      | getLevel (I.Pi (_, U)) = getLevel U
      | getLevel (I.Root _)  = I.Type
      | getLevel (I.Redex (U, _)) = getLevel U
      | getLevel (I.Lam (_, U)) = getLevel U
      | getLevel (I.EClo (U,_)) = getLevel U

     checkType (V) = () if G |- V : type

       Invariant: G |- V : L' for some L'
    
    fun checkType V =
        (case getLevel V
           of I.Type => ()
            | _ => raise Error ""Typing ambiguous -- free type variable"")
    *)
  (* abstractKPi (K, V) = V'
       where V' = {{K}} V

       Invariant:
       If   {{K}} |- V : L
       and  . ||- V

       then V' = {{K}} V
       and  . |- V' : L
       and  . ||- V'
    *)
  (* enforced by reconstruction -kw
          val _ = checkType V'' *)
  (* enforced by reconstruction -kw
          val _ = checkType V'' *)
  (* abstractKLam (K, U) = U'
       where U' = [[K]] U

       Invariant:
       If   {{K}} |- U : V
       and  . ||- U
       and  . ||- V

       then U' = [[K]] U
       and  . |- U' : {{K}} V
       and  . ||- U'
    *)
  (* enforced by reconstruction -kw
          val _ = checkType V'' *)
  (* enforced by reconstruction -kw
          val _ = checkType V'' *)
  (* abstractDecImp V = (k', V')    rename --cs  (see above) 

       Invariant:
       If    . |- V : L
       and   K ||- V

       then  . |- V' : L
       and   V' = {{K}} V
       and   . ||- V'
       and   k' = |K|
    *)
  (* abstractDef  (U, V) = (k', (U', V'))

       Invariant:
       If    . |- V : L
       and   . |- U : V
       and   K1 ||- V
       and   K2 ||- U
       and   K = K1, K2

       then  . |- V' : L
       and   V' = {{K}} V
       and   . |- U' : V'
       and   U' = [[K]] U
       and   . ||- V'
       and   . ||- U'
       and   k' = |K|
    *)
  (* abstractCtxs [G1,...,Gn] = G0, [G1',...,Gn']
       Invariants:
       If . |- G1,...,Gn ctx
          K ||- G1,...,Gn for some K
       then G0 |- G1',...,Gn' ctx for G0 = {{K}}
       and G1',...,Gn' nf
       and . ||- G1',...,Gn' ctx
    *)
  (* closedDec (G, D) = true iff D contains no EVar or FVar *)
  (* collectEVars (G, U[s], Xs) = Xs'
       Invariants:
         G |- U[s] : V
         Xs' extends Xs by new EVars in U[s]
    *)
  (* for the theorem prover:
       collect and abstract in subsitutions  including residual lemmas
       pending approval of Frank.
    *)
  (* abstractPVar (K, depth, L) = C'

       Invariant:
       If   G |- L : V
       and  |G| = depth
       and  L occurs in K  at kth position (starting at 1)
       then C' = Bidx (depth + k)
       and  {{K}}, G |- C' : V
    *)
  (* TC cannot contain free FVAR's or EVars'
            --cs  Fri Apr 30 13:45:50 2004 *)
  (* Argument must be in normal form *)
  (* enforced by reconstruction -kw
          val _ = checkType V'' *)
  (* enforced by reconstruction -kw
          val _ = checkType V'' *)
  (* What's happening with GX? *)
  (* What's happening with TCs? *)
  (* just added to abstract over residual lemmas  -cs *)
  (* Tomorrow: Make collection in program values a priority *)
  (* Then just traverse the Tomega by abstraction to get to the types of those
       variables. *)
  let raiseType = raiseType
  let raiseTerm = raiseTerm
  let piDepend = piDepend
  let closedDec = closedDec
  let closedSub = closedSub
  let closedExp = closedExp
  let abstractDecImp = abstractDecImp
  let abstractDef = abstractDef
  let abstractCtxs = abstractCtxs
  let abstractTomegaSub = abstractTomegaSub
  let abstractTomegaPrg = abstractTomegaPrg
  let abstractSpine s_ s = abstractSpineExt (s_, s)
  let collectEVars = collectEVars
  let collectEVarsSpine = collectEVarsSpine
  let closedCtx = closedCtx
  let closedCTX = closedCTX
end
(* functor Abstract *)

(* # 1 "src/lambda/Abstract.sml.ml" *)
