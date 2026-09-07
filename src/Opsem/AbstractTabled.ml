open! Intsyn.Lambda_
open! Print.Print_
open! Compile
open! CompSyn

(* # 1 "src/opsem/AbstractTabled.sig.ml" *)
open TableParam

(* Abstraction *)
(* Author: Brigitte Pientka *)
include ABSTRACTTABLED
(* signature ABSTRACTTABLED *)

(* # 1 "src/opsem/AbstractTabled.fun.ml" *)
open! Basis

(* Abstraction *)
(* Author: Frank Pfenning, Carsten Schuermann *)
(* Modified: Roberto Virga, Brigitte Pientka *)
exception Error of string

let () =
  Printexc.register_printer (function Error msg -> Some msg | _ -> None)

module AbstractTabled (AbstractTabled__0 : sig
  (*! structure IntSyn' : INTSYN !*)
  module Whnf : WHNF

  (*! sharing Whnf.IntSyn = IntSyn' !*)
  module Unify : UNIFY

  (*! sharing Unify.IntSyn = IntSyn' !*)
  module Constraints : CONSTRAINTS

  (*! sharing Constraints.IntSyn = IntSyn' !*)
  module Subordinate : Subordinate.Subordinate_.SUBORDINATE

  (*! sharing Subordinate.IntSyn = IntSyn' !*)
  module Print : PRINT

  (*! sharing Print.IntSyn = IntSyn' !*)
  module Conv : CONV
end) : ABSTRACTTABLED = struct
  open AbstractTabled__0

  (*! structure IntSyn = IntSyn' !*)
  (*! structure TableParam = TableParam !*)
  exception Error = Error

  open! struct
    module I = IntSyn
    module C = CompSyn

    type duplicates = Av of I.exp * int | Fgn of int
    type seenIn = TypeLabel | Body [@@deriving eq, ord, show]
    type existVars = Ev of I.exp

    let rec lengthSub = function
      | I.Shift n -> 0
      | I.Dot (e, s) -> 1 + lengthSub s

    let rec compose' (a, g) = match a with
      | I.Null -> g
      | IntSyn.Decl (g', d) -> IntSyn.Decl (compose' (g', g), d)

    let rec isId = function
      | I.Shift n -> n = 0
      | I.Dot (I.Idx n, s') as s -> isId' (s, 0)
      | I.Dot (I.Undef, s') as s -> isId' (s, 0)
      | I.Dot (I.Exp _, s) -> false

    and isId' (a, k) = match a with
      | I.Shift n -> n = k
      | I.Dot (I.Idx i, s) ->
          let k' = k + 1 in
          i = k' && isId' (s, k')
      | I.Dot (I.Undef, s) -> isId' (s, k + 1)

    let rec equalCtx (a, s, b, s') = match a, b with
      | I.Null, I.Null -> true
      | I.Decl (g, d), I.Decl (g', d') ->
          Conv.convDec d s (d', s')
          && equalCtx (g, I.dot1 s, g', I.dot1 s')
      | I.Decl (g, d), I.Null -> false
      | I.Null, I.Decl (g', d') -> false

    let eqEVarW arg__1 arg__2 =
      begin match (arg__1, arg__2) with
      | I.EVar (r1, _, _, _), Ev (I.EVar (r2, _, _, _)) -> r1 == r2
      | _, _ -> false
      end

    let eqEVar x1 (Ev x2) =
      let x1', s = Whnf.whnf (x1, I.id) in
      let x2', s = Whnf.whnf (x2, I.id) in
      eqEVarW x1' (Ev x2')

    let member' p k =
      let rec exists' = function
        | I.Null -> None
        | I.Decl (k', (l, Ev y)) ->
            begin if p (Ev y) then Some l else exists' k'
            end
      in
      exists' k

    let member p k =
      let rec exists' = function
        | I.Null -> None
        | I.Decl (k', (i, y)) ->
            begin if p y then Some i else exists' k'
            end
      in
      exists' k

    let update' p k =
      let rec update' = function
        | I.Null -> I.Null
        | I.Decl (k', (label, y)) ->
            begin if p y then I.Decl (k', (Body, y))
            else I.Decl (update' k', (label, y))
            end
      in
      update' k

    let update p k =
      let rec update' = function
        | I.Null -> I.Null
        | I.Decl (k', ((label, i), y)) ->
            begin if p y then I.Decl (k', ((Body, i), y))
            else I.Decl (update' k', ((label, i), y))
            end
      in
      update' k

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
      | I.FgnExp (csid, csfe) ->
          I.FgnExpStd.fold csid csfe
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

    let rec reverseCtx = function
      | I.Null, g -> g
      | I.Decl (g, d), g' -> reverseCtx (g, I.Decl (g', d))

    let rec ctxToEVarSub (a, s) = match a with
      | I.Null -> s
      | IntSyn.Decl (g, IntSyn.Dec (_, a)) ->
          let s' = ctxToEVarSub (g, s) in
          let x = IntSyn.newEVar IntSyn.Null (I.EClo (a, s')) in
          IntSyn.Dot (IntSyn.Exp x, s')

    let rec collectExpW (gss, gl, a, k, dupVars, flag, d) = match a with
      | (I.Uni l, s) -> (k, dupVars)
      | (I.Pi ((d_, _), v), s) ->
          let k', _ = collectDec (gss, (d_, s), (k, dupVars), d, false) in
          collectExp
            ( gss,
              I.Decl (gl, I.decSub d_ s),
              (v, I.dot1 s),
              k',
              dupVars,
              flag,
              d )
      | (I.Root (_, s_), s) ->
          collectSpine (gss, gl, (s_, s), k, dupVars, flag, d)
      | (I.Lam (d_, u), s) ->
          let k', _ = collectDec (gss, (d_, s), (k, dupVars), d, false) in
          collectExp
            ( gss,
              I.Decl (gl, I.decSub d_ s),
              (u, I.dot1 s),
              k',
              dupVars,
              flag,
              d + 1 )
      | ((I.EVar (r, gx, v, cnstrs) as x), s)
        ->
          collectEVar (gss, gl, (x, s), k, dupVars, flag, d)
      | (I.FgnExp (csid, csfe), s) ->
          I.FgnExpStd.fold csid csfe
            (function
              | u, kd' ->
                  let k', dup = kd' in
                  collectExp (gss, gl, (u, s), k', dup, false, d))
            (k, I.Decl (dupVars, Fgn d))

    and collectExp (gss, gl, us, k, dupVars, flag, d) =
      collectExpW (gss, gl, Whnf.whnf us, k, dupVars, flag, d)

    and collectSpine (gss, gl, a, k, dupVars, flag, d) = match a with
      | (I.Nil, _) -> (k, dupVars)
      | (I.SClo (s_, s'), s) ->
          collectSpine (gss, gl, (s_, I.comp s' s), k, dupVars, flag, d)
      | (I.App (u, s_), s) ->
          let k', dupVars' =
            collectExp (gss, gl, (u, s), k, dupVars, flag, d)
          in
          collectSpine (gss, gl, (s_, s), k', dupVars', flag, d)

    and collectEVarFapStr
        ( gss,
          gl,
          ((x', v'), w),
          ((I.EVar (r, gx, v, cnstrs) as x), s),
          k,
          dupVars,
          flag,
          d ) =
      begin match member' (eqEVar x) k with
      | Some label ->
          begin if flag then
            collectSub (gss, gl, s, k, I.Decl (dupVars, Av (x, d)), flag, d)
          else collectSub (gss, gl, s, k, dupVars, flag, d)
          end
      | None ->
          let label =
            begin if flag then Body else TypeLabel
            end
          in
          let k', dupVars' =
            collectExp
              ((I.Null, I.id), I.Null, (v', I.id), k, dupVars, false, d)
          in
          collectSub
            ( gss,
              gl,
              I.comp w s,
              I.Decl (k', (label, Ev x')),
              dupVars',
              flag,
              d )
      end

    and collectEVarNFapStr
        ( gss,
          gl,
          ((x', v'), w),
          ((I.EVar (r, gx, v, cnstrs) as x), s),
          k,
          dupVars,
          flag,
          d ) =
      begin match member' (eqEVar x) k with
      | Some label ->
          begin if flag then
            collectSub (gss, gl, s, k, I.Decl (dupVars, Av (x, d)), flag, d)
          else collectSub (gss, gl, s, k, dupVars, flag, d)
          end
      | None ->
          let label =
            begin if flag then Body else TypeLabel
            end
          in
          let k', dupVars' =
            collectExp
              ((I.Null, I.id), I.Null, (v', I.id), k, dupVars, false, d)
          in
          begin if flag then
            collectSub
              ( gss,
                gl,
                I.comp w s,
                I.Decl (k', (label, Ev x')),
                I.Decl (dupVars', Av (x', d)),
                flag,
                d )
          else
            collectSub
              ( gss,
                gl,
                I.comp w s,
                I.Decl (k', (label, Ev x')),
                dupVars',
                flag,
                d )
          end
      end

    and collectEVarStr
        ( ((gs, ss) as gss),
          gl,
          ((I.EVar (r, gx, v, cnstrs) as x), s),
          k,
          dupVars,
          flag,
          d ) =
      let w = Subordinate.weaken gx (I.targetFam v) in
      let iw = Whnf.invert w in
      let gx' = Whnf.strengthen iw gx in
      let (I.EVar (r', _, _, _) as x') = I.newEVar gx' (I.EClo (v, iw)) in
      ignore (Unify.instantiateEVar r (I.EClo (x', w)) []);
      let v' = raiseType gx' (I.EClo (v, iw)) in
      begin if isId (I.comp w (I.comp ss s)) then
        collectEVarFapStr
          (gss, gl, ((x', v'), w), (x, s), k, dupVars, flag, d)
      else
        collectEVarNFapStr
          (gss, gl, ((x', v'), w), (x, s), k, dupVars, flag, d)
      end

    and collectEVarFap
        (gss, gl, ((I.EVar (r, gx, v, cnstrs) as x), s), k, dupVars, flag, d)
        =
      begin match member (eqEVar x) k with
      | Some label ->
          begin if flag then
            collectSub (gss, gl, s, k, I.Decl (dupVars, Av (x, d)), flag, d)
          else collectSub (gss, gl, s, k, dupVars, flag, d)
          end
      | None ->
          let label =
            begin if flag then Body else TypeLabel
            end
          in
          let v' = raiseType gx v in
          let k', dupVars' =
            collectExp
              ((I.Null, I.id), I.Null, (v', I.id), k, dupVars, false, d)
          in
          collectSub
            (gss, gl, s, I.Decl (k', (label, Ev x)), dupVars', flag, d)
      end

    and collectEVarNFap
        (gss, gl, ((I.EVar (r, gx, v, cnstrs) as x), s), k, dupVars, flag, d)
        =
      begin match member' (eqEVar x) k with
      | Some label ->
          begin if flag then
            collectSub (gss, gl, s, k, I.Decl (dupVars, Av (x, d)), flag, d)
          else collectSub (gss, gl, s, k, dupVars, flag, d)
          end
      | None ->
          let label =
            begin if flag then Body else TypeLabel
            end
          in
          let v' = raiseType gx v in
          let k', dupVars' =
            collectExp
              ((I.Null, I.id), I.Null, (v', I.id), k, dupVars, false, d)
          in
          begin if flag then
            collectSub
              ( gss,
                gl,
                s,
                I.Decl (k', (label, Ev x)),
                I.Decl (dupVars, Av (x, d)),
                flag,
                d )
          else
            collectSub
              (gss, gl, s, I.Decl (k', (label, Ev x)), dupVars, flag, d)
          end
      end

    and collectEVar
        (gss, gl, ((I.EVar (r, gx, v, cnstrs) as x), s), k, dupVars, flag, d)
        =
      begin if !TableParam.strengthen then
        collectEVarStr (gss, gl, (x, s), k, dupVars, flag, d)
      else
        begin if isId s then
          collectEVarFap (gss, gl, (x, s), k, dupVars, flag, d)
        else collectEVarNFap (gss, gl, (x, s), k, dupVars, flag, d)
        end
      end

    and collectDec (gss, (I.Dec (_, v), s), (k, dupVars), d, flag) =
      let k', dupVars' =
        collectExp (gss, I.Null, (v, s), k, dupVars, flag, d)
      in
      (k', dupVars')

    and collectSub (gss, gl, a, k, dupVars, flag, d) = match a with
      | I.Shift _ -> (k, dupVars)
      | I.Dot (I.Idx _, s) ->
          collectSub (gss, gl, s, k, dupVars, flag, d)
      | I.Dot (I.Exp (I.EVar ({ contents = Some u }, _, _, _) as x), s) ->
          let u' = Whnf.normalize (u, I.id) in
          let k', dupVars' =
            collectExp (gss, gl, (u', I.id), k, dupVars, flag, d)
          in
          collectSub (gss, gl, s, k', dupVars', flag, d)
      | I.Dot (I.Exp (I.AVar { contents = Some u' } as u), s) ->
          let k', dupVars' =
            collectExp (gss, gl, (u', I.id), k, dupVars, flag, d)
          in
          collectSub (gss, gl, s, k', dupVars', flag, d)
      | I.Dot (I.Exp (I.EClo (u', s')), s) ->
          let u = Whnf.normalize (u', s') in
          let k', dupVars' =
            collectExp (gss, gl, (u, I.id), k, dupVars, flag, d)
          in
          collectSub (gss, gl, s, k', dupVars', flag, d)
      | I.Dot (I.Exp u, s) ->
          let k', dupVars' =
            collectExp (gss, gl, (u, I.id), k, dupVars, flag, d)
          in
          collectSub (gss, gl, s, k', dupVars', flag, d)
      | I.Dot (I.Undef, s) ->
          collectSub (gss, gl, s, k, dupVars, flag, d)

    let rec collectCtx (gss, a, b, d) = match a, b with
      | C.DProg (I.Null, I.Null), (k, dupVars) -> (k, dupVars)
      | C.DProg (I.Decl (g, d_), I.Decl (dPool, parameter)), (k, dupVars) ->
          let k', dupVars' =
            collectCtx (gss, C.DProg (g, dPool), (k, dupVars), d - 1)
          in
          collectDec (gss, (d_, I.id), (k', dupVars'), d - 1, false)
      | C.DProg (I.Decl (g, d_), I.Decl (dPool, C.Dec (r, s, ha))), (k, dupVars) ->
          let k', dupVars' =
            collectCtx (gss, C.DProg (g, dPool), (k, dupVars), d - 1)
          in
          collectDec (gss, (d_, I.id), (k', dupVars'), d - 1, false)

    let rec abstractExpW (flag, a, b, vars, gl, total, depth, c, eqn) = match a, b, c with
      | gs, posEA, ((I.Uni l as u), s)
        ->
          (posEA, vars, u, eqn)
      | gs, posEA, (I.Pi ((d, p), v), s) ->
          let posEA', vars', d, _ =
            abstractDec (gs, posEA, vars, gl, total, depth, (d, s), None)
          in
          let posEA'', vars'', v', eqn2 =
            abstractExp
              ( flag,
                gs,
                posEA',
                vars',
                gl,
                total,
                depth + 1,
                (v, I.dot1 s),
                eqn )
          in
          (posEA'', vars'', piDepend d p v', eqn2)
      | gs, posEA, (I.Root (h, s_), s) ->
          let posEA', vars', s_, eqn' =
            abstractSpine
              (flag, gs, posEA, vars, gl, total, depth, (s_, s), eqn)
          in
          (posEA', vars', I.Root (h, s_), eqn')
      | gs, posEA, (I.Lam (d, u), s) ->
          let posEA', vars', d', _ =
            abstractDec (gs, posEA, vars, gl, total, depth, (d, s), None)
          in
          let posEA'', vars'', u', eqn2 =
            abstractExp
              ( flag,
                gs,
                posEA',
                vars',
                I.Decl (gl, d'),
                total,
                depth + 1,
                (u, I.dot1 s),
                eqn )
          in
          (posEA'', vars'', I.Lam (d', u'), eqn2)
      | ((gss, ss) as gs), ((epos, apos) as posEA), ((I.EVar (_, gx, vx, _) as x), s) ->
          begin if isId (I.comp ss s) then
            abstractEVarFap
              (flag, gs, posEA, vars, gl, total, depth, (x, s), eqn)
          else
            abstractEVarNFap
              (flag, gs, posEA, vars, gl, total, depth, (x, s), eqn)
          end

    and abstractExp (flag, gs, posEA, vars, gl, total, depth, us, eqn) =
      abstractExpW
        (flag, gs, posEA, vars, gl, total, depth, Whnf.whnf us, eqn)

    and abstractEVarFap
        ( flag,
          gs,
          ((epos, apos) as posEA),
          vars,
          gl,
          total,
          depth,
          (x, s),
          eqn ) =
      begin match member (eqEVar x) vars with
      | Some (label, i) ->
          begin if flag then
            begin match label with
            | Body ->
                let bv = I.BVar (apos + depth) in
                let bv' = I.BVar (i + depth) in
                let bv1 = I.BVar (apos + depth) in
                let posEA', vars', s_, eqn1 =
                  abstractSub
                    ( flag,
                      gs,
                      (epos, apos - 1),
                      vars,
                      gl,
                      total,
                      depth,
                      s,
                      I.Nil,
                      eqn )
                in
                ( posEA',
                  vars',
                  I.Root (bv, I.Nil),
                  TableParam.Unify
                    (gl, I.Root (bv', s_), I.Root (bv1, I.Nil), eqn1) )
            | TypeLabel ->
                let vars' = update (eqEVar x) vars in
                let posEA', vars'', s_, eqn1 =
                  abstractSub
                    ( flag,
                      gs,
                      (epos, apos),
                      vars',
                      gl,
                      total,
                      depth,
                      s,
                      I.Nil,
                      eqn )
                in
                (posEA', vars'', I.Root (I.BVar (i + depth), s_), eqn1)
            end
          else
            let posEA', vars', s_, eqn1 =
              abstractSub
                ( flag,
                  gs,
                  (epos, apos),
                  vars,
                  gl,
                  total,
                  depth,
                  s,
                  I.Nil,
                  eqn )
            in
            (posEA', vars', I.Root (I.BVar (i + depth), s_), eqn1)
          end
      | None ->
          let label =
            begin if flag then Body else TypeLabel
            end
          in
          let bv = I.BVar (epos + depth) in
          let pos = (epos - 1, apos) in
          let posEA', vars', s_, eqn1 =
            abstractSub
              ( flag,
                gs,
                pos,
                I.Decl (vars, ((label, epos), Ev x)),
                gl,
                total,
                depth,
                s,
                I.Nil,
                eqn )
          in
          (posEA', vars', I.Root (bv, s_), eqn1)
      end

    and abstractEVarNFap
        ( flag,
          gs,
          ((epos, apos) as posEA),
          vars,
          gl,
          total,
          depth,
          (x, s),
          eqn ) =
      begin match member (eqEVar x) vars with
      | Some (label, i) ->
          begin if flag then
            let bv = I.BVar (apos + depth) in
            let bv' = I.BVar (i + depth) in
            let bv1 = I.BVar (apos + depth) in
            let posEA', vars', s_, eqn1 =
              abstractSub
                ( flag,
                  gs,
                  (epos, apos - 1),
                  vars,
                  gl,
                  total,
                  depth,
                  s,
                  I.Nil,
                  eqn )
            in
            ( posEA',
              vars',
              I.Root (bv, I.Nil),
              TableParam.Unify (gl, I.Root (bv', s_), I.Root (bv1, I.Nil), eqn1)
            )
          else
            let posEA', vars', s_, eqn1 =
              abstractSub
                ( flag,
                  gs,
                  (epos, apos),
                  vars,
                  gl,
                  total,
                  depth,
                  s,
                  I.Nil,
                  eqn )
            in
            (posEA', vars', I.Root (I.BVar (i + depth), s_), eqn1)
          end
      | None ->
          begin if flag then
            let label =
              begin if flag then Body else TypeLabel
              end
            in
            let bv = I.BVar (apos + depth) in
            let bv' = I.BVar (epos + depth) in
            let bv1 = I.BVar (apos + depth) in
            let posEA', vars', s_, eqn1 =
              abstractSub
                ( flag,
                  gs,
                  (epos - 1, apos - 1),
                  I.Decl (vars, ((label, epos), Ev x)),
                  gl,
                  total,
                  depth,
                  s,
                  I.Nil,
                  eqn )
            in
            ( posEA',
              vars',
              I.Root (bv, I.Nil),
              TableParam.Unify (gl, I.Root (bv', s_), I.Root (bv1, I.Nil), eqn1)
            )
          else
            let posEA', vars', s_, eqn1 =
              abstractSub
                ( flag,
                  gs,
                  (epos - 1, apos),
                  I.Decl (vars, ((TypeLabel, epos), Ev x)),
                  gl,
                  total,
                  depth,
                  s,
                  I.Nil,
                  eqn )
            in
            (posEA', vars', I.Root (I.BVar (epos + depth), s_), eqn1)
          end
      end

    and abstractSub (flag, gs, posEA, vars, gl, total, depth, a, s_, eqn) = match a with
      | I.Shift k ->
          begin if k < depth then
            abstractSub
              ( flag,
                gs,
                posEA,
                vars,
                gl,
                total,
                depth,
                I.Dot (I.Idx (k + 1), I.Shift (k + 1)),
                s_,
                eqn )
          else (posEA, vars, s_, eqn)
          end
      | I.Dot (I.Idx k, s)
        ->
          abstractSub
            ( flag,
              gs,
              posEA,
              vars,
              gl,
              total,
              depth,
              s,
              I.App (I.Root (I.BVar k, I.Nil), s_),
              eqn )
      | I.Dot (I.Exp u, s)
        ->
          let posEA', vars', u', eqn' =
            abstractExp
              (flag, gs, posEA, vars, gl, total, depth, (u, I.id), eqn)
          in
          abstractSub
            ( flag,
              gs,
              posEA',
              vars',
              gl,
              total,
              depth,
              s,
              I.App (u', s_),
              eqn' )

    and abstractSpine (flag, gs, posEA, vars, gl, total, depth, a, eqn) = match a with
      | (I.Nil, _) ->
          (posEA, vars, I.Nil, eqn)
      | (I.SClo (s_, s'), s) ->
          abstractSpine
            ( flag,
              gs,
              posEA,
              vars,
              gl,
              total,
              depth,
              (s_, I.comp s' s),
              eqn )
      | (I.App (u, s_), s) ->
          let posEA', vars', u', eqn' =
            abstractExp
              (flag, gs, posEA, vars, gl, total, depth, (u, s), eqn)
          in
          let posEA'', vars'', s', eqn'' =
            abstractSpine
              (flag, gs, posEA', vars', gl, total, depth, (s_, s), eqn')
          in
          (posEA'', vars'', I.App (u', s'), eqn'')

    and abstractSub' (flag, gs, epos, vars, total, a) = match a with
      | I.Shift k ->
          begin if k < 0 then raise (Error "Substitution out of range\n")
          else (epos, vars, I.Shift (k + total))
          end
      | I.Dot (I.Idx k, s) ->
          let epos', vars', s' =
            abstractSub' (flag, gs, epos, vars, total, s)
          in
          (epos', vars', I.Dot (I.Idx k, s'))
      | I.Dot (I.Exp u, s) ->
          let (ep, _), vars', u', _ =
            abstractExp
              ( false,
                gs,
                (epos, 0),
                vars,
                I.Null,
                total,
                0,
                (u, I.id),
                TableParam.Trivial )
          in
          let epos'', vars'', s' =
            abstractSub' (flag, gs, ep, vars', total, s)
          in
          (epos'', vars'', I.Dot (I.Exp u', s'))

    and abstractDec (gs, posEA, vars, gl, total, depth, a, b) = match a, b with
      | (I.Dec (x, v), s), None ->
          let posEA', vars', v', eqn =
            abstractExp
              ( false,
                gs,
                posEA,
                vars,
                gl,
                total,
                depth,
                (v, s),
                TableParam.Trivial )
          in
          (posEA', vars', I.Dec (x, v'), eqn)
      | (I.Dec (x, v), s), Some eqn ->
          let posEA', vars', v', eqn' =
            abstractExp
              (true, gs, posEA, vars, gl, total, depth, (v, s), eqn)
          in
          (posEA', vars', I.Dec (x, v'), eqn')

    let rec abstractCtx' (gs, epos, vars, total, depth, a, g', eqn) = match a with
      | C.DProg (I.Null, I.Null) ->
          (epos, vars, g', eqn)
      | C.DProg (I.Decl (g, d_), I.Decl (dPool, parameter)) ->
          let d = IntSyn.ctxLength g in
          let (epos', _), vars', d', _ =
            abstractDec
              ( gs,
                (epos, total),
                vars,
                I.Null,
                total,
                depth - 1,
                (d_, I.id),
                None )
          in
          abstractCtx'
            ( gs,
              epos',
              vars',
              total,
              depth - 1,
              C.DProg (g, dPool),
              I.Decl (g', d'),
              eqn )
      | C.DProg (I.Decl (g, d_), I.Decl (dPool, _)) ->
          let d = IntSyn.ctxLength g in
          let (epos', _), vars', d', _ =
            abstractDec
              ( gs,
                (epos, total),
                vars,
                I.Null,
                total,
                depth - 1,
                (d_, I.id),
                None )
          in
          abstractCtx'
            ( gs,
              epos',
              vars',
              total,
              depth - 1,
              C.DProg (g, dPool),
              I.Decl (g', d'),
              eqn )

    let abstractCtx (gs, epos, vars, total, depth, dProg) =
      abstractCtx'
        (gs, epos, vars, total, depth, dProg, I.Null, TableParam.Trivial)

    let rec makeEVarCtx (gs, vars, dEVars, a, total) = match a with
      | I.Null -> dEVars
      | I.Decl (k', (_, Ev (I.EVar (_, gx, vx, _) as e))) ->
          let v' = raiseType gx vx in
          let _, vars', v'', _ =
            abstractExp
              ( false,
                gs,
                (0, 0),
                vars,
                I.Null,
                0,
                total - 1,
                (v', I.id),
                TableParam.Trivial )
          in
          let dEVars' = makeEVarCtx (gs, vars', dEVars, k', total - 1) in
          let dEVars'' = I.Decl (dEVars', I.Dec (None, v'')) in
          dEVars''

    let makeAVarCtx (vars, dupVars) =
      let rec avarCtx (vars, a, k) = match a with
        | I.Null -> I.Null
        | I.Decl (k', Av ((I.EVar ({ contents = None }, gx, vx, _) as e), d)) ->
            I.Decl
              ( avarCtx (vars, k', k + 1),
                I.ADec
                  ( Some ((("AVar " ^ Int.toString k) ^ "--") ^ Int.toString d),
                    d ) )
        | I.Decl (k', Av ((I.EVar (_, gx, vx, _) as e), d)) ->
            I.Decl
              ( avarCtx (vars, k', k + 1),
                I.ADec
                  ( Some ((("AVar " ^ Int.toString k) ^ "--") ^ Int.toString d),
                    d ) )
      in
      avarCtx (vars, dupVars, 0)

    let rec lowerEVar' (x, g, vs') = match vs' with
      | (I.Pi ((d', _), v'), s') ->
          let d'' = I.decSub d' s' in
          let x', u =
            lowerEVar' (x, I.Decl (g, d''), Whnf.whnf (v', I.dot1 s'))
          in
          (x', I.Lam (d'', u))
      | vs' ->
          let x' = x in
          (x', x')

    and lowerEVar1 = function
      | x, I.EVar (r, g, _, _), ((I.Pi _ as v), s) ->
          let x', u = lowerEVar' (x, g, (v, s)) in
          I.EVar (ref (Some u), I.Null, v, ref [])
      | _, x, _ -> x

    and lowerEVar (e, a) = match a with
      | (I.EVar (r, g, v, { contents = [] }) as x) ->
          lowerEVar1 (e, x, Whnf.whnf (v, I.id))
      | I.EVar _ ->
          raise
            (Error
               "abstraction : LowerEVars: Typing ambiguous -- constraint of \
                functional type cannot be simplified")

    let rec evarsToSub (a, s) = match a with
      | I.Null -> s
      | I.Decl
            ( k',
              (_, Ev (I.EVar (({ contents = None } as i), gx, vx, cnstr) as e))
            ) ->
          let v' = raiseType gx vx in
          let x =
            lowerEVar1
              (e, I.EVar (i, I.Null, v', cnstr), Whnf.whnf (v', I.id))
          in
          let s' = evarsToSub (k', s) in
          I.Dot (I.Exp x, s')

    let rec avarsToSub (a, s) = match a with
      | I.Null -> s
      | I.Decl (vars', Av ((I.EVar (i, gx, vx, cnstr) as e), d)) ->
          let s' = avarsToSub (vars', s) in
          let (I.AVar r as x') = I.newAVar () in
          I.Dot (I.Exp (I.EClo (x', I.Shift (-d))), s')

    let abstractEVarCtx (C.DProg (g, dPool) as dp) p s =
      let gs, ss, d =
        begin if !TableParam.strengthen then
          let w' = Subordinate.weaken g (I.targetFam p) in
          let iw = Whnf.invert w' in
          let g' = Whnf.strengthen iw g in
          let d' = I.ctxLength g' in
          (g', iw, d')
        else (g, I.id, I.ctxLength g)
        end
      in
      let k, dupVars = collectCtx ((gs, ss), dp, (I.Null, I.Null), d) in
      let k', dupVars' =
        collectExp ((gs, ss), I.Null, (p, s), k, dupVars, true, d)
      in
      let epos = I.ctxLength k' in
      let apos = I.ctxLength dupVars' in
      let total = epos + apos in
      let epos', vars', g', eqn =
        abstractCtx ((gs, ss), epos, I.Null, total, d, dp)
      in
      let posEA'', vars'', u', eqn' =
        abstractExp
          (true, (gs, ss), (epos', total), vars', I.Null, total, d, (p, s), eqn)
      in
      let dAVars = makeAVarCtx (vars'', dupVars') in
      let dEVars = makeEVarCtx ((gs, ss), vars'', I.Null, vars'', 0) in
      let s' = avarsToSub (dupVars', I.id) in
      let s'' = evarsToSub (vars'', s') in
      let g'' = reverseCtx (g', I.Null) in
      begin if !TableParam.strengthen then
        let w' = Subordinate.weaken g'' (I.targetFam u') in
        let iw = Whnf.invert w' in
        let gs' = Whnf.strengthen iw g'' in
        (gs', dAVars, dEVars, u', eqn', s'')
      else (g'', dAVars, dEVars, u', eqn', s'')
      end
  end

  (*
       We write {{K}} for the context of K, where EVars have
       been translated to declarations and their occurrences to BVars.
       For each occurrence of EVar in U, we generate a distinct BVar together with
       a residual constraint. This enforces that the final abstraction of U is
       linear. However, we do not linearize the context G.

       We write {{U}}_K, {{S}}_K for the corresponding translation of an
       expression or spine.

       Just like contexts G, any K is implicitly assumed to be
       well-formed and in dependency Order.

       We write  K ||- U  if all EVars in U are collected in K.
       In particular, . ||- U means U contains no EVars.  Similarly,
       for spines K ||- S and other syntactic categories.

       Collection and abstraction raise Error if there are unresolved
       constraints after simplification.
    *)
  (* eqEVar X Y = B
     where B iff X and Y represent same variable
     *)
  (* Sun Dec  1 14:04:17 2002 -bp  may raise exception
       if strengthening is applied,i.e. the substitution is not always id! *)
  (* a few helper functions to manage K *)
  (* member P K = B option *)
  (* member P K = B option *)
  (* member P K = B option *)
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
  (* collectExpW ((Gs, ss), Gl, (U, s), K, DupVars, flag) = (K', DupVars')

       Invariant:
       If    G, Gl |- s : G1     G1 |- U : V      (U,s) in whnf
                Gs |- ss : G  (Gs is the strengthened context and ss is the strengthening substitution)

       No circularities in U
             (enforced by extended occurs-check for FVars in Unify)
       and   K' = K, K''
             where K' contains all EVars in (U,s)
       and  DupVars' = DupVars, DupVars''
            where DupVars' contains all duplicates in (U,s)

      if flag = true
        then duplicates of EVars are collected in DupVars
        otherwise no duplicates are collected

      note : 1) we only need to collect duplicate occurrences of EVars
                if we need to linearize the term the EVars occur in.

             2) we do not linearize fgnExp
    *)
  (* Possible optimization: Calculate also the normal form of the term *)
  (* should we apply I.dot1(ss) ? Tue Oct 15 21:55:16 2002 -bp *)
  (* No other cases can occur due to whnf invariant *)
  (* collectExp (Gss, G, Gl, (U, s), K) = K'
       same as collectExpW  but  (U,s) need not to be in whnf
    *)
  (* collectSpine (Gss, Gl, (S, s), K, DupVars, flag) = (K', DupVars')

       Invariant:
       If    G, Gl |- s : G1     G1 |- S : V > P
                Gs |- ss : G
       then  K' = K, K'' and DupVars' = DupVars, DupVars''
       where K'' contains all EVars in (S, s)
       and DupVars'' contains all duplicates in (S, s)
     *)
  (* we have seen X before *)
  (* case label of
                     Body => collectSub(Gss, Gl, s, K, I.Decl(DupVars, AV(X,d)), flag, d)
                   | TypeLabel =>
                       let
                         val K' = update' (eqEVar X) K
                       in
                         collectSub(Gss, Gl, s, K', DupVars, flag, d)
                       end *)
  (* since X has occurred before, we do not traverse its type V' *)
  (*          val V' = raiseType (GX, V)  inefficient! *)
  (* we have seen X before, i.e. it was already strengthened *)
  (* -bp this is a possible optimization for the variant case
                   case label of
                   Body => (print ""Collect DupVar\n""; collectSub(Gss, Gl, s, K, I.Decl(DupVars, AV(X, d)), flag, d) )
                 | TypeLabel =>
                    let
                      val _ = print ""TypeLabel\n""
                      val K' = update' (eqEVar X) K
                    in
                      collectSub(Gss, Gl, s, K', DupVars, flag, d)
                    end*)
  (* val V' = raiseType (GX, V)  inefficient! *)
  (* ? *)
  (* equalCtx (Gs, I.id, GX', s) *)
  (* fully applied *)
  (* not fully applied *)
  (* X is fully applied pattern *)
  (* we have seen X before *)
  (*
                 case label of
                   Body => collectSub(Gss, Gl, s, K, I.Decl(DupVars, AV(X, d)), flag, d)
                 | TypeLabel =>
                     let
                       val K' = update' (eqEVar X) K
                     in
                       collectSub(Gss, Gl, s, K', DupVars, flag, d)
                     end *)
  (* since X has occurred before, we do not traverse its type V' *)
  (* val _ = checkEmpty !cnstrs *)
  (* inefficient! *)
  (* case label of
                   Body => collectSub(Gss, Gl, s, K, I.Decl(DupVars, AV(X, d)), flag, d)
                   | TypeLabel =>
                     let
                       val K' = update' (eqEVar X) K
                     in
                       collectSub(Gss, Gl, s, K', DupVars, flag, d)
                     end             *)
  (* inefficient! *)
  (* equalCtx (compose'(Gl, G), s, GX, s)  *)
  (* X is fully applied *)
  (* X is not fully applied *)
  (* collectDec (Gss, G, (x:V, s), K, DupVars, flag) = (K', DupVars')

       Invariant:
       If    G |- s : G1     G1 |- V : L
            Gs |- ss : G
       then  K' = K, K'' and DupVars' = DupVars, DupVars''
       where K'' contains all EVars in (V, s)
       and DupVars'' contains all duplicates in (S, s)
    *)
  (*      val (K',DupVars') =  collectExp (Gss, I.Null, (V, s), K, I.Null, false, d)*)
  (* collectSub (G, s, K, DupVars, flag) = (K', DupVars)

       Invariant:
       If    G |- s : G1

       then  K' = K, K'' and DupVars' = DupVars, DupVars''
       where K'' contains all EVars in s
       and DupVars'' contains all duplicates in s
    *)
  (* inefficient? *)
  (* inefficient? *)
  (* collectCtx (Gss, G0, G, K) = (K', DupVars)
       Invariant:
       If G0 |- G ctx,
       then G0' = G0,G
       and K' = K, K'' where K'' contains all EVars in G
    *)
  (* abstractExpW (epos, apos, Vars, Gl, total, depth, (U, s), eqn) = (epos', apos', Vars', U', eqn')
      (abstraction and linearization of existential variables in (U,s))

       U' = {{U[s]}}_(K, Dup)

       Invariant:
       If     G, Gl |- U[s] : V and  U[s] is in whnf
       and   |Gl| = depth
             |Dup, K| = total

       and epos = (total(K) + l) - #replaced expressions in U    (generate no additional constraints)
       and apos = (total(Dup) + + total(K) + l) - #replaced expressions in U
                  (generate additional constraints (avars))

       and Vars'  = Vars, Vars''
           where Vars contains pairs ((label, i), EV X) of all EVars (EV X),
           where label refers to where we have seen the existential variable (typeLabel or body) and
           i corresponds to the bvar-index assigned to X in U[s]

       and   K ~ Vars (we can obtain K from Vars by dropping the first component of
             each pair (_, EV X) in Vars' )

       then   {{Dup}}, {{K}}  ||- U
       and {{Dup}} {{K}} , G, Gl |-  U' : V'
       and eqn' = eqn, eqn'' where eqn'' are residual equations relating between elements
           in {{K}} and {{Dup}}

       and . ||- Pi G. U'  and   U' is in nf

       if flag then linearize U else allow duplicates.

    *)
  (* X is possibly strengthened ! *)
  (* X is fully applied *)
  (* s =/= id, i.e. X is not fully applied *)
  (*      | abstractExpW (posEA, Vars, Gl, total, depth, (X as I.FgnExp (cs, ops), s), eqn) =  *)
  (*      let
          val (X, _) = #map(ops) (fn U => abstractExp (posEA, Vars, Gl, total, depth, (U, s), eqn))
        in        abstractFgn (posEA, Vars, Gl, total, depth, X, eqn)
        end
*)
  (* abstractExp (posEA, Vars, Gl, total, depth, (U, s)) = U'

       same as abstractExpW, but (U,s) need not to be in whnf
    *)
  (* we have seen X before *)
  (* enforce linearization *)
  (* do not enforce linearization -- used for type labels *)
  (* we see X for the first time *)
  (* we have seen X before *)
  (* enforce linearization *)
  (* (case label of
               Body =>
                 let
                  val _ = print ""abstractEVarNFap -- flag true; we have seen X before\n""
                   val BV = I.BVar(apos + depth)
                   val BV' = I.BVar(i + depth)
                   val BV1 = I.BVar(apos + depth)
                   val (posEA', Vars', S, eqn1) = abstractSub (flag, Gs, (epos, apos - 1), Vars, Gl, total, depth, s, I.Nil, eqn)
                 in
                   (posEA', Vars', I.Root(BV, I.Nil), TableParam.Unify(Gl, I.Root(BV', S), I.Root(BV1, I.Nil ), eqn1))
                 end
              | TyeLabel =>
                 let
                   val Vars' = update (eqEVar X) Vars
                   val (posEA', Vars'', S, eqn1) = abstractSub (flag, Gs, (epos, apos), Vars', Gl, total, depth, s, I.Nil, eqn)
                 in
                   (posEA', Vars'', I.Root(I.BVar(i + depth), S), eqn1)
                 end) *)
  (* do not enforce linearization -- used for type labels *)
  (* we have not seen X before *)
  (* enforce linearization since X is not fully applied *)
  (* do not enforce linearization -- used for type labels *)
  (* abstractSub (flag, Gs, posEA, Vars, Gl, total, depth, s, S, eqn) = (posEA', Vars', S', eqn')

       (implicit raising)
       (for posEA, Vars, eqn explanation see above)

       let K* = K, Dup

       S' = {{s}}_K* @@ S

       Invariant:
       If    G, Gl |- s : G1
       and  |Gl| = depth

       and   {{Dup}} {{K}} ||- s
       then {{Dup}} {{K}}, G, Gl |- S' : {G1}.W > W   (for some W)
       and  . ||- S'
    *)
  (* k = depth *)
  (* abstractSpine (flag, Gs, posEA, Vars, Gl, total, depth, (S, s), eqn) = (posEA', Vars', S', eqn')
       where S' = {{S[s]}}_K*   and K* = K, Dup

       Invariant:
       If   Gl, G |- s : G1     G1 |- S : V > P
       and  K* ||- S
       and  |G| = depth

       then {{K*}}, G, G |- S' : V' > P'
       and  . ||- S'
    *)
  (* abstractSub' (flag, Gs, epos, K, Gl, total, s) = (epos', K', s')      (implicit raising)

        Invariant:
        If   G |- s : G1
       and  |G| = depth
       and  K ||- s
       and {{K}}, G |- {{s}}_K : G1
       then Gs, G |- s' : G1    where  s' == {{s}}_K

         *)
  (* abstractDec (Gs, posEA, Vars, Gl, total, depth, (x:V, s)) = (posEA', Vars', x:V')
       where V = {{V[s]}}_K*

       Invariant:
       If   G |- s : G1     G1 |- V : L
       and  K* ||- V
       and  |G| = depth

       then {{K*}}, G |- V' : L
       and  . ||- V'
    *)
  (*      val (posEA', Vars', V', _) = abstractExp (false, Gs, posEA, Vars, Gl, total, depth, (V, s), TableParam.Trivial)*)
  (*      val (posEA', Vars', V', _) = abstractExp (false, Gs, posEA, Vars, Gl, total, depth, (V, s), TableParam.Trivial)*)
  (* abstractCtx (Gs, epos, K, total, depth, C.DProg(G,dPool)) = (epos', K', G')
       where G' = {{G}}_K

       Invariants:
       If K ||- G
       and |G| = depth
       then {{K}} |- G' ctx
       and . ||- G'
       and epos = current epos

       note: we will linearize all dynamic assumptions in G.
    *)
  (*        let
          val d = IntSyn.ctxLength (G)
          val ((epos', _), Vars', D', eqn') = abstractDec (Gs, (epos, total), Vars, I.Null, total , depth - 1, (D, I.id), SOME(eqn))
        in
          abstractCtx' (Gs, epos', Vars', total, depth - 1, C.DProg(G, dPool), I.Decl (G', D'), eqn')
        end
*)
  (* makeEVarCtx (Gs, Kall, D, K, eqn) = G'  *)
  (* add case for foreign expressions ? *)
  (* lowerEVar' (G, V[s]) = (X', U), see lowerEVar *)
  (* lowerEVar1 (X, V[s]), V[s] in whnf, see lowerEVar *)
  (* lowerEVar1 (X, I.EVar (r, G, _, _), (V as I.Pi _, s)) = *)
  (* lowerEVar (X) = X'

       Invariant:
       If   G |- X : {{G'}} P
            X not subject to any constraints
       then G, G' |- X' : P

       Effect: X is instantiated to [[G']] X' if G' is empty
               otherwise X = X' and no effect occurs.
    *)
  (* It is not clear if this case can happen *)
  (* pre-Stelf 1.2 code walk, Fri May  8 11:05:08 1998 *)
  (* evarsToSub (K, s') = s
      Invariant:
      if K = EV Xn ... EV X2, EV X1
        then
        s = X1 . X2 . ... s'
     *)
  (* redundant ? *)
  (* evarsToSub (K, s') = s
      Invariant:
      if K = AV Xn ... AV X2, EV X1
        then
        s = X1 . X2 . ... s'
     *)
  (* abstractEVarCtx (G, p, s) = (G', D', U', s')

     if G |- p[s] and s contains free variables X_n .... X_1
     then
       D' |- Pi  G' . U'
       where D' is the abstraction over the free vars X_n .... X_1

       and s' is a substitution the free variables
            X_n .... X_1, s.t.

       . |- s' : D'

       . |- (Pi G' .U' )[s']  is equivalent to . |- Pi G . p[s]

       Note: G' and U' are possibly strengthened
   *)
  (* K ||- G i.e. K contains all EVars in G *)
  (* DupVars' , K' ||- p[s]  i.e. K' contains all EVars in (p,s) and G and
                                         DupVars' contains all duplicate EVars p[s] *)
  (* {{G}}_Vars' , i.e. abstract over the existential variables in G*)
  (* = 0 *)
  (* abstract over existential variables in p[s] and linearize the expression *)
  (* depth *)
  (* note: depth will become negative during makeEVarCtx *)
  let abstractEVarCtx = abstractEVarCtx

  (* abstractAnswSub s = (D', s')

   if  |- s : Delta' and s may contain free variables and
     D |- Pi G. U  and  |- s : D and  |- (Pi G . U)[s]
    then

    D' |- s' : D   where D' contains all the
    free variables from s
   *)
  let abstractAnswSub = function
    | s ->
        let k, _ =
          collectSub ((I.Null, I.id), I.Null, s, I.Null, I.Null, false, 0)
        in
        let epos = I.ctxLength k in
        let _, vars, s' (*0 *) =
          abstractSub' (false, (I.Null, I.id), epos, I.Null, epos, s)
          (* total *)
        in
        let dEVars = makeEVarCtx ((I.Null, I.id), vars, I.Null, vars, 0) in
        let s1' = ctxToEVarSub (dEVars, I.id) in
        (dEVars, s')
  (* no linearization for answer substitution *)

  let raiseType g u = raiseType g u
end
(*! sharing Conv.IntSyn = IntSyn' !*)
(*! structure TableParam : TABLEPARAM !*)
(*! sharing TableParam.IntSyn = IntSyn' !*)
(* functor AbstractTabled *)

(* # 1 "src/opsem/AbstractTabled.sml.ml" *)
