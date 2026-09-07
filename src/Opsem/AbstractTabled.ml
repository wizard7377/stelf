open! Basis
open! Global
open! Global.Global_
open! Table
open! Table.Table_
open! Intsyn
open! Intsyn.Lambda_
open! Names
open! Names.Names_
open! Print
open! Print.Print_
open! Formatter
open! Formatter__Formatter_
open! Index
open! Index.Index_
open! Typecheck
open! Typecheck.Typecheck_
open! Solvers
open! Solvers.Solvers_
open! Subordinate
open! Subordinate
open! Compile
open! Compile.Compile_
open! CompSyn
open! Assign
open! Tabling

(* # 1 "src/opsem/AbstractTabled.sig.ml" *)
open! Basis
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
      | I.Dot (e_, s) -> 1 + lengthSub s

    let rec compose' (a, g_) = match a with
      | I.Null -> g_
      | IntSyn.Decl (g'_, d_) -> IntSyn.Decl (compose' (g'_, g_), d_)

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
      | I.Decl (g_, d_), I.Decl (g'_, d'_) ->
          Conv.convDec (d_, s) (d'_, s')
          && equalCtx (g_, I.dot1 s, g'_, I.dot1 s')
      | I.Decl (g_, d_), I.Null -> false
      | I.Null, I.Decl (g'_, d'_) -> false

    let eqEVarW arg__1 arg__2 =
      begin match (arg__1, arg__2) with
      | I.EVar (r1, _, _, _), Ev (I.EVar (r2, _, _, _)) -> r1 == r2
      | _, _ -> false
      end

    let eqEVar x1_ (Ev x2_) =
      let x1', s = Whnf.whnf (x1_, I.id) in
      let x2', s = Whnf.whnf (x2_, I.id) in
      eqEVarW x1' (Ev x2')

    let member' p_ k_ =
      let rec exists' = function
        | I.Null -> None
        | I.Decl (k'_, (l, Ev y_)) ->
            begin if p_ (Ev y_) then Some l else exists' k'_
            end
      in
      exists' k_

    let member p_ k_ =
      let rec exists' = function
        | I.Null -> None
        | I.Decl (k'_, (i, y_)) ->
            begin if p_ y_ then Some i else exists' k'_
            end
      in
      exists' k_

    let update' p_ k_ =
      let rec update' = function
        | I.Null -> I.Null
        | I.Decl (k'_, (label, y_)) ->
            begin if p_ y_ then I.Decl (k'_, (Body, y_))
            else I.Decl (update' k'_, (label, y_))
            end
      in
      update' k_

    let update p_ k_ =
      let rec update' = function
        | I.Null -> I.Null
        | I.Decl (k'_, ((label, i), y_)) ->
            begin if p_ y_ then I.Decl (k'_, ((Body, i), y_))
            else I.Decl (update' k'_, ((label, i), y_))
            end
      in
      update' k_

    let ( or ) = function
      | I.Maybe, _ -> I.Maybe
      | _, I.Maybe -> I.Maybe
      | I.Meta, _ -> I.Meta
      | _, I.Meta -> I.Meta
      | I.No, I.No -> I.No

    let rec occursInExp (k, a) = match a with
      | I.Uni _ -> I.No
      | I.Pi (dp_, v_) ->
          ( or ) (occursInDecP (k, dp_), occursInExp (k + 1, v_))
      | I.Root (h_, s_) -> occursInHead (k, h_, occursInSpine (k, s_))
      | I.Lam (d_, v_) ->
          ( or ) (occursInDec (k, d_), occursInExp (k + 1, v_))
      | I.FgnExp (csid_, csfe) ->
          I.FgnExpStd.fold csid_ csfe
            (function
              | u_, dp_ ->
                  ( or ) (dp_, occursInExp (k, Whnf.normalize (u_, I.id))))
            I.No

    and occursInHead (k, a, dp_) = match a, dp_ with
      | I.BVar k', dp_ ->
          begin if k = k' then I.Maybe else dp_
          end
      | I.Const _, dp_ -> dp_
      | I.Def _, dp_ -> dp_
      | I.FgnConst _, dp_ -> dp_
      | I.Skonst _, I.No -> I.No
      | I.Skonst _, I.Meta -> I.Meta
      | I.Skonst _, I.Maybe -> I.Meta

    and occursInSpine = function
      | _, I.Nil -> I.No
      | k, I.App (u_, s_) -> ( or ) (occursInExp (k, u_), occursInSpine (k, s_))

    and occursInDec (k, I.Dec (_, v_)) = occursInExp (k, v_)
    and occursInDecP (k, (d_, _)) = occursInDec (k, d_)

    let piDepend a1 b1 = match a1, b1 with
      | (d_, I.No), v_ -> I.Pi ((d_, I.No), v_)
      | (d_, I.Meta), v_ -> I.Pi ((d_, I.Meta), v_)
      | (d_, I.Maybe), v_ -> I.Pi ((d_, occursInExp (1, v_)), v_)

    let rec raiseType a1 b1 = match a1, b1 with
      | I.Null, v_ -> v_
      | I.Decl (g_, d_), v_ -> raiseType g_ (I.Pi ((d_, I.Maybe), v_))

    let rec reverseCtx = function
      | I.Null, g_ -> g_
      | I.Decl (g_, d_), g'_ -> reverseCtx (g_, I.Decl (g'_, d_))

    let rec ctxToEVarSub (a, s) = match a with
      | I.Null -> s
      | IntSyn.Decl (g_, IntSyn.Dec (_, a_)) ->
          let s' = ctxToEVarSub (g_, s) in
          let x_ = IntSyn.newEVar IntSyn.Null (I.EClo (a_, s')) in
          IntSyn.Dot (IntSyn.Exp x_, s')

    let rec collectExpW (gss, gl_, a, k_, dupVars, flag, d) = match a with
      | (I.Uni l_, s) -> (k_, dupVars)
      | (I.Pi ((d_, _), v_), s) ->
          let k'_, _ = collectDec (gss, (d_, s), (k_, dupVars), d, false) in
          collectExp
            ( gss,
              I.Decl (gl_, I.decSub d_ s),
              (v_, I.dot1 s),
              k'_,
              dupVars,
              flag,
              d )
      | (I.Root (_, s_), s) ->
          collectSpine (gss, gl_, (s_, s), k_, dupVars, flag, d)
      | (I.Lam (d_, u_), s) ->
          let k'_, _ = collectDec (gss, (d_, s), (k_, dupVars), d, false) in
          collectExp
            ( gss,
              I.Decl (gl_, I.decSub d_ s),
              (u_, I.dot1 s),
              k'_,
              dupVars,
              flag,
              d + 1 )
      | ((I.EVar (r, gx, v_, cnstrs) as x_), s)
        ->
          collectEVar (gss, gl_, (x_, s), k_, dupVars, flag, d)
      | (I.FgnExp (csid_, csfe), s) ->
          I.FgnExpStd.fold csid_ csfe
            (function
              | u_, kd' ->
                  let k'_, dup = kd' in
                  collectExp (gss, gl_, (u_, s), k'_, dup, false, d))
            (k_, I.Decl (dupVars, Fgn d))

    and collectExp (gss, gl_, us_, k_, dupVars, flag, d) =
      collectExpW (gss, gl_, Whnf.whnf us_, k_, dupVars, flag, d)

    and collectSpine (gss, gl_, a, k_, dupVars, flag, d) = match a with
      | (I.Nil, _) -> (k_, dupVars)
      | (I.SClo (s_, s'), s) ->
          collectSpine (gss, gl_, (s_, I.comp s' s), k_, dupVars, flag, d)
      | (I.App (u_, s_), s) ->
          let k'_, dupVars' =
            collectExp (gss, gl_, (u_, s), k_, dupVars, flag, d)
          in
          collectSpine (gss, gl_, (s_, s), k'_, dupVars', flag, d)

    and collectEVarFapStr
        ( gss,
          gl_,
          ((x'_, v'_), w),
          ((I.EVar (r, gx, v_, cnstrs) as x_), s),
          k_,
          dupVars,
          flag,
          d ) =
      begin match member' (eqEVar x_) k_ with
      | Some label ->
          begin if flag then
            collectSub (gss, gl_, s, k_, I.Decl (dupVars, Av (x_, d)), flag, d)
          else collectSub (gss, gl_, s, k_, dupVars, flag, d)
          end
      | None ->
          let label =
            begin if flag then Body else TypeLabel
            end
          in
          let k'_, dupVars' =
            collectExp
              ((I.Null, I.id), I.Null, (v'_, I.id), k_, dupVars, false, d)
          in
          collectSub
            ( gss,
              gl_,
              I.comp w s,
              I.Decl (k'_, (label, Ev x'_)),
              dupVars',
              flag,
              d )
      end

    and collectEVarNFapStr
        ( gss,
          gl_,
          ((x'_, v'_), w),
          ((I.EVar (r, gx, v_, cnstrs) as x_), s),
          k_,
          dupVars,
          flag,
          d ) =
      begin match member' (eqEVar x_) k_ with
      | Some label ->
          begin if flag then
            collectSub (gss, gl_, s, k_, I.Decl (dupVars, Av (x_, d)), flag, d)
          else collectSub (gss, gl_, s, k_, dupVars, flag, d)
          end
      | None ->
          let label =
            begin if flag then Body else TypeLabel
            end
          in
          let k'_, dupVars' =
            collectExp
              ((I.Null, I.id), I.Null, (v'_, I.id), k_, dupVars, false, d)
          in
          begin if flag then
            collectSub
              ( gss,
                gl_,
                I.comp w s,
                I.Decl (k'_, (label, Ev x'_)),
                I.Decl (dupVars', Av (x'_, d)),
                flag,
                d )
          else
            collectSub
              ( gss,
                gl_,
                I.comp w s,
                I.Decl (k'_, (label, Ev x'_)),
                dupVars',
                flag,
                d )
          end
      end

    and collectEVarStr
        ( ((gs_, ss) as gss),
          gl_,
          ((I.EVar (r, gx, v_, cnstrs) as x_), s),
          k_,
          dupVars,
          flag,
          d ) =
      let w = Subordinate.weaken gx (I.targetFam v_) in
      let iw = Whnf.invert w in
      let gx' = Whnf.strengthen iw gx in
      let (I.EVar (r', _, _, _) as x'_) = I.newEVar gx' (I.EClo (v_, iw)) in
      ignore (Unify.instantiateEVar r (I.EClo (x'_, w)) []);
      let v'_ = raiseType gx' (I.EClo (v_, iw)) in
      begin if isId (I.comp w (I.comp ss s)) then
        collectEVarFapStr
          (gss, gl_, ((x'_, v'_), w), (x_, s), k_, dupVars, flag, d)
      else
        collectEVarNFapStr
          (gss, gl_, ((x'_, v'_), w), (x_, s), k_, dupVars, flag, d)
      end

    and collectEVarFap
        (gss, gl_, ((I.EVar (r, gx, v_, cnstrs) as x_), s), k_, dupVars, flag, d)
        =
      begin match member (eqEVar x_) k_ with
      | Some label ->
          begin if flag then
            collectSub (gss, gl_, s, k_, I.Decl (dupVars, Av (x_, d)), flag, d)
          else collectSub (gss, gl_, s, k_, dupVars, flag, d)
          end
      | None ->
          let label =
            begin if flag then Body else TypeLabel
            end
          in
          let v'_ = raiseType gx v_ in
          let k'_, dupVars' =
            collectExp
              ((I.Null, I.id), I.Null, (v'_, I.id), k_, dupVars, false, d)
          in
          collectSub
            (gss, gl_, s, I.Decl (k'_, (label, Ev x_)), dupVars', flag, d)
      end

    and collectEVarNFap
        (gss, gl_, ((I.EVar (r, gx, v_, cnstrs) as x_), s), k_, dupVars, flag, d)
        =
      begin match member' (eqEVar x_) k_ with
      | Some label ->
          begin if flag then
            collectSub (gss, gl_, s, k_, I.Decl (dupVars, Av (x_, d)), flag, d)
          else collectSub (gss, gl_, s, k_, dupVars, flag, d)
          end
      | None ->
          let label =
            begin if flag then Body else TypeLabel
            end
          in
          let v'_ = raiseType gx v_ in
          let k'_, dupVars' =
            collectExp
              ((I.Null, I.id), I.Null, (v'_, I.id), k_, dupVars, false, d)
          in
          begin if flag then
            collectSub
              ( gss,
                gl_,
                s,
                I.Decl (k'_, (label, Ev x_)),
                I.Decl (dupVars, Av (x_, d)),
                flag,
                d )
          else
            collectSub
              (gss, gl_, s, I.Decl (k'_, (label, Ev x_)), dupVars, flag, d)
          end
      end

    and collectEVar
        (gss, gl_, ((I.EVar (r, gx, v_, cnstrs) as x_), s), k_, dupVars, flag, d)
        =
      begin if !TableParam.strengthen then
        collectEVarStr (gss, gl_, (x_, s), k_, dupVars, flag, d)
      else
        begin if isId s then
          collectEVarFap (gss, gl_, (x_, s), k_, dupVars, flag, d)
        else collectEVarNFap (gss, gl_, (x_, s), k_, dupVars, flag, d)
        end
      end

    and collectDec (gss, (I.Dec (_, v_), s), (k_, dupVars), d, flag) =
      let k'_, dupVars' =
        collectExp (gss, I.Null, (v_, s), k_, dupVars, flag, d)
      in
      (k'_, dupVars')

    and collectSub (gss, gl_, a, k_, dupVars, flag, d) = match a with
      | I.Shift _ -> (k_, dupVars)
      | I.Dot (I.Idx _, s) ->
          collectSub (gss, gl_, s, k_, dupVars, flag, d)
      | I.Dot (I.Exp (I.EVar ({ contents = Some u_ }, _, _, _) as x_), s) ->
          let u'_ = Whnf.normalize (u_, I.id) in
          let k'_, dupVars' =
            collectExp (gss, gl_, (u'_, I.id), k_, dupVars, flag, d)
          in
          collectSub (gss, gl_, s, k'_, dupVars', flag, d)
      | I.Dot (I.Exp (I.AVar { contents = Some u'_ } as u_), s) ->
          let k'_, dupVars' =
            collectExp (gss, gl_, (u'_, I.id), k_, dupVars, flag, d)
          in
          collectSub (gss, gl_, s, k'_, dupVars', flag, d)
      | I.Dot (I.Exp (I.EClo (u'_, s')), s) ->
          let u_ = Whnf.normalize (u'_, s') in
          let k'_, dupVars' =
            collectExp (gss, gl_, (u_, I.id), k_, dupVars, flag, d)
          in
          collectSub (gss, gl_, s, k'_, dupVars', flag, d)
      | I.Dot (I.Exp u_, s) ->
          let k'_, dupVars' =
            collectExp (gss, gl_, (u_, I.id), k_, dupVars, flag, d)
          in
          collectSub (gss, gl_, s, k'_, dupVars', flag, d)
      | I.Dot (I.Undef, s) ->
          collectSub (gss, gl_, s, k_, dupVars, flag, d)

    let rec collectCtx (gss, a, b, d) = match a, b with
      | C.DProg (I.Null, I.Null), (k_, dupVars) -> (k_, dupVars)
      | C.DProg (I.Decl (g_, d_), I.Decl (dPool, parameter_)), (k_, dupVars) ->
          let k'_, dupVars' =
            collectCtx (gss, C.DProg (g_, dPool), (k_, dupVars), d - 1)
          in
          collectDec (gss, (d_, I.id), (k'_, dupVars'), d - 1, false)
      | C.DProg (I.Decl (g_, d_), I.Decl (dPool, C.Dec (r, s, ha))), (k_, dupVars) ->
          let k'_, dupVars' =
            collectCtx (gss, C.DProg (g_, dPool), (k_, dupVars), d - 1)
          in
          collectDec (gss, (d_, I.id), (k'_, dupVars'), d - 1, false)

    let rec abstractExpW (flag, a, b, vars_, gl_, total, depth, c, eqn) = match a, b, c with
      | gs_, posEA, ((I.Uni l_ as u_), s)
        ->
          (posEA, vars_, u_, eqn)
      | gs_, posEA, (I.Pi ((d_, p_), v_), s) ->
          let posEA', vars', d_, _ =
            abstractDec (gs_, posEA, vars_, gl_, total, depth, (d_, s), None)
          in
          let posEA'', vars'', v'_, eqn2 =
            abstractExp
              ( flag,
                gs_,
                posEA',
                vars',
                gl_,
                total,
                depth + 1,
                (v_, I.dot1 s),
                eqn )
          in
          (posEA'', vars'', piDepend (d_, p_) v'_, eqn2)
      | gs_, posEA, (I.Root (h_, s_), s) ->
          let posEA', vars', s_, eqn' =
            abstractSpine
              (flag, gs_, posEA, vars_, gl_, total, depth, (s_, s), eqn)
          in
          (posEA', vars', I.Root (h_, s_), eqn')
      | gs_, posEA, (I.Lam (d_, u_), s) ->
          let posEA', vars', d'_, _ =
            abstractDec (gs_, posEA, vars_, gl_, total, depth, (d_, s), None)
          in
          let posEA'', vars'', u'_, eqn2 =
            abstractExp
              ( flag,
                gs_,
                posEA',
                vars',
                I.Decl (gl_, d'_),
                total,
                depth + 1,
                (u_, I.dot1 s),
                eqn )
          in
          (posEA'', vars'', I.Lam (d'_, u'_), eqn2)
      | ((gss, ss) as gs_), ((epos, apos) as posEA), ((I.EVar (_, gx, vx, _) as x_), s) ->
          begin if isId (I.comp ss s) then
            abstractEVarFap
              (flag, gs_, posEA, vars_, gl_, total, depth, (x_, s), eqn)
          else
            abstractEVarNFap
              (flag, gs_, posEA, vars_, gl_, total, depth, (x_, s), eqn)
          end

    and abstractExp (flag, gs_, posEA, vars_, gl_, total, depth, us_, eqn) =
      abstractExpW
        (flag, gs_, posEA, vars_, gl_, total, depth, Whnf.whnf us_, eqn)

    and abstractEVarFap
        ( flag,
          gs_,
          ((epos, apos) as posEA),
          vars_,
          gl_,
          total,
          depth,
          (x_, s),
          eqn ) =
      begin match member (eqEVar x_) vars_ with
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
                      gs_,
                      (epos, apos - 1),
                      vars_,
                      gl_,
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
                    (gl_, I.Root (bv', s_), I.Root (bv1, I.Nil), eqn1) )
            | TypeLabel ->
                let vars' = update (eqEVar x_) vars_ in
                let posEA', vars'', s_, eqn1 =
                  abstractSub
                    ( flag,
                      gs_,
                      (epos, apos),
                      vars',
                      gl_,
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
                  gs_,
                  (epos, apos),
                  vars_,
                  gl_,
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
                gs_,
                pos,
                I.Decl (vars_, ((label, epos), Ev x_)),
                gl_,
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
          gs_,
          ((epos, apos) as posEA),
          vars_,
          gl_,
          total,
          depth,
          (x_, s),
          eqn ) =
      begin match member (eqEVar x_) vars_ with
      | Some (label, i) ->
          begin if flag then
            let bv = I.BVar (apos + depth) in
            let bv' = I.BVar (i + depth) in
            let bv1 = I.BVar (apos + depth) in
            let posEA', vars', s_, eqn1 =
              abstractSub
                ( flag,
                  gs_,
                  (epos, apos - 1),
                  vars_,
                  gl_,
                  total,
                  depth,
                  s,
                  I.Nil,
                  eqn )
            in
            ( posEA',
              vars',
              I.Root (bv, I.Nil),
              TableParam.Unify (gl_, I.Root (bv', s_), I.Root (bv1, I.Nil), eqn1)
            )
          else
            let posEA', vars', s_, eqn1 =
              abstractSub
                ( flag,
                  gs_,
                  (epos, apos),
                  vars_,
                  gl_,
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
                  gs_,
                  (epos - 1, apos - 1),
                  I.Decl (vars_, ((label, epos), Ev x_)),
                  gl_,
                  total,
                  depth,
                  s,
                  I.Nil,
                  eqn )
            in
            ( posEA',
              vars',
              I.Root (bv, I.Nil),
              TableParam.Unify (gl_, I.Root (bv', s_), I.Root (bv1, I.Nil), eqn1)
            )
          else
            let posEA', vars', s_, eqn1 =
              abstractSub
                ( flag,
                  gs_,
                  (epos - 1, apos),
                  I.Decl (vars_, ((TypeLabel, epos), Ev x_)),
                  gl_,
                  total,
                  depth,
                  s,
                  I.Nil,
                  eqn )
            in
            (posEA', vars', I.Root (I.BVar (epos + depth), s_), eqn1)
          end
      end

    and abstractSub (flag, gs_, posEA, vars_, gl_, total, depth, a, s_, eqn) = match a with
      | I.Shift k ->
          begin if k < depth then
            abstractSub
              ( flag,
                gs_,
                posEA,
                vars_,
                gl_,
                total,
                depth,
                I.Dot (I.Idx (k + 1), I.Shift (k + 1)),
                s_,
                eqn )
          else (posEA, vars_, s_, eqn)
          end
      | I.Dot (I.Idx k, s)
        ->
          abstractSub
            ( flag,
              gs_,
              posEA,
              vars_,
              gl_,
              total,
              depth,
              s,
              I.App (I.Root (I.BVar k, I.Nil), s_),
              eqn )
      | I.Dot (I.Exp u_, s)
        ->
          let posEA', vars', u'_, eqn' =
            abstractExp
              (flag, gs_, posEA, vars_, gl_, total, depth, (u_, I.id), eqn)
          in
          abstractSub
            ( flag,
              gs_,
              posEA',
              vars',
              gl_,
              total,
              depth,
              s,
              I.App (u'_, s_),
              eqn' )

    and abstractSpine (flag, gs_, posEA, vars_, gl_, total, depth, a, eqn) = match a with
      | (I.Nil, _) ->
          (posEA, vars_, I.Nil, eqn)
      | (I.SClo (s_, s'), s) ->
          abstractSpine
            ( flag,
              gs_,
              posEA,
              vars_,
              gl_,
              total,
              depth,
              (s_, I.comp s' s),
              eqn )
      | (I.App (u_, s_), s) ->
          let posEA', vars', u'_, eqn' =
            abstractExp
              (flag, gs_, posEA, vars_, gl_, total, depth, (u_, s), eqn)
          in
          let posEA'', vars'', s'_, eqn'' =
            abstractSpine
              (flag, gs_, posEA', vars', gl_, total, depth, (s_, s), eqn')
          in
          (posEA'', vars'', I.App (u'_, s'_), eqn'')

    and abstractSub' (flag, gs_, epos, vars_, total, a) = match a with
      | I.Shift k ->
          begin if k < 0 then raise (Error "Substitution out of range\n")
          else (epos, vars_, I.Shift (k + total))
          end
      | I.Dot (I.Idx k, s) ->
          let epos', vars', s' =
            abstractSub' (flag, gs_, epos, vars_, total, s)
          in
          (epos', vars', I.Dot (I.Idx k, s'))
      | I.Dot (I.Exp u_, s) ->
          let (ep, _), vars', u'_, _ =
            abstractExp
              ( false,
                gs_,
                (epos, 0),
                vars_,
                I.Null,
                total,
                0,
                (u_, I.id),
                TableParam.Trivial )
          in
          let epos'', vars'', s' =
            abstractSub' (flag, gs_, ep, vars', total, s)
          in
          (epos'', vars'', I.Dot (I.Exp u'_, s'))

    and abstractDec (gs_, posEA, vars_, gl_, total, depth, a, b) = match a, b with
      | (I.Dec (x, v_), s), None ->
          let posEA', vars', v'_, eqn =
            abstractExp
              ( false,
                gs_,
                posEA,
                vars_,
                gl_,
                total,
                depth,
                (v_, s),
                TableParam.Trivial )
          in
          (posEA', vars', I.Dec (x, v'_), eqn)
      | (I.Dec (x, v_), s), Some eqn ->
          let posEA', vars', v'_, eqn' =
            abstractExp
              (true, gs_, posEA, vars_, gl_, total, depth, (v_, s), eqn)
          in
          (posEA', vars', I.Dec (x, v'_), eqn')

    let rec abstractCtx' (gs_, epos, vars_, total, depth, a, g'_, eqn) = match a with
      | C.DProg (I.Null, I.Null) ->
          (epos, vars_, g'_, eqn)
      | C.DProg (I.Decl (g_, d_), I.Decl (dPool, parameter_)) ->
          let d = IntSyn.ctxLength g_ in
          let (epos', _), vars', d'_, _ =
            abstractDec
              ( gs_,
                (epos, total),
                vars_,
                I.Null,
                total,
                depth - 1,
                (d_, I.id),
                None )
          in
          abstractCtx'
            ( gs_,
              epos',
              vars',
              total,
              depth - 1,
              C.DProg (g_, dPool),
              I.Decl (g'_, d'_),
              eqn )
      | C.DProg (I.Decl (g_, d_), I.Decl (dPool, _)) ->
          let d = IntSyn.ctxLength g_ in
          let (epos', _), vars', d'_, _ =
            abstractDec
              ( gs_,
                (epos, total),
                vars_,
                I.Null,
                total,
                depth - 1,
                (d_, I.id),
                None )
          in
          abstractCtx'
            ( gs_,
              epos',
              vars',
              total,
              depth - 1,
              C.DProg (g_, dPool),
              I.Decl (g'_, d'_),
              eqn )

    let abstractCtx (gs_, epos, vars_, total, depth, dProg) =
      abstractCtx'
        (gs_, epos, vars_, total, depth, dProg, I.Null, TableParam.Trivial)

    let rec makeEVarCtx (gs_, vars_, dEVars, a, total) = match a with
      | I.Null -> dEVars
      | I.Decl (k'_, (_, Ev (I.EVar (_, gx, vx, _) as e_))) ->
          let v'_ = raiseType gx vx in
          let _, vars', v'', _ =
            abstractExp
              ( false,
                gs_,
                (0, 0),
                vars_,
                I.Null,
                0,
                total - 1,
                (v'_, I.id),
                TableParam.Trivial )
          in
          let dEVars' = makeEVarCtx (gs_, vars', dEVars, k'_, total - 1) in
          let dEVars'' = I.Decl (dEVars', I.Dec (None, v'')) in
          dEVars''

    let makeAVarCtx (vars_, dupVars) =
      let rec avarCtx (vars_, a, k) = match a with
        | I.Null -> I.Null
        | I.Decl (k'_, Av ((I.EVar ({ contents = None }, gx, vx, _) as e_), d)) ->
            I.Decl
              ( avarCtx (vars_, k'_, k + 1),
                I.ADec
                  ( Some ((("AVar " ^ Int.toString k) ^ "--") ^ Int.toString d),
                    d ) )
        | I.Decl (k'_, Av ((I.EVar (_, gx, vx, _) as e_), d)) ->
            I.Decl
              ( avarCtx (vars_, k'_, k + 1),
                I.ADec
                  ( Some ((("AVar " ^ Int.toString k) ^ "--") ^ Int.toString d),
                    d ) )
      in
      avarCtx (vars_, dupVars, 0)

    let rec lowerEVar' (x_, g_, vs'_) = match vs'_ with
      | (I.Pi ((d'_, _), v'_), s') ->
          let d''_ = I.decSub d'_ s' in
          let x'_, u_ =
            lowerEVar' (x_, I.Decl (g_, d''_), Whnf.whnf (v'_, I.dot1 s'))
          in
          (x'_, I.Lam (d''_, u_))
      | vs'_ ->
          let x'_ = x_ in
          (x'_, x'_)

    and lowerEVar1 = function
      | x_, I.EVar (r, g_, _, _), ((I.Pi _ as v_), s) ->
          let x'_, u_ = lowerEVar' (x_, g_, (v_, s)) in
          I.EVar (ref (Some u_), I.Null, v_, ref [])
      | _, x_, _ -> x_

    and lowerEVar (e_, a) = match a with
      | (I.EVar (r, g_, v_, { contents = [] }) as x_) ->
          lowerEVar1 (e_, x_, Whnf.whnf (v_, I.id))
      | I.EVar _ ->
          raise
            (Error
               "abstraction : LowerEVars: Typing ambiguous -- constraint of \
                functional type cannot be simplified")

    let rec evarsToSub (a, s) = match a with
      | I.Null -> s
      | I.Decl
            ( k'_,
              (_, Ev (I.EVar (({ contents = None } as i_), gx, vx, cnstr) as e_))
            ) ->
          let v'_ = raiseType gx vx in
          let x_ =
            lowerEVar1
              (e_, I.EVar (i_, I.Null, v'_, cnstr), Whnf.whnf (v'_, I.id))
          in
          let s' = evarsToSub (k'_, s) in
          I.Dot (I.Exp x_, s')

    let rec avarsToSub (a, s) = match a with
      | I.Null -> s
      | I.Decl (vars', Av ((I.EVar (i_, gx, vx, cnstr) as e_), d)) ->
          let s' = avarsToSub (vars', s) in
          let (I.AVar r as x'_) = I.newAVar () in
          I.Dot (I.Exp (I.EClo (x'_, I.Shift (-d))), s')

    let abstractEVarCtx (C.DProg (g_, dPool) as dp) p s =
      let gs_, ss, d =
        begin if !TableParam.strengthen then
          let w' = Subordinate.weaken g_ (I.targetFam p) in
          let iw = Whnf.invert w' in
          let g'_ = Whnf.strengthen iw g_ in
          let d' = I.ctxLength g'_ in
          (g'_, iw, d')
        else (g_, I.id, I.ctxLength g_)
        end
      in
      let k_, dupVars = collectCtx ((gs_, ss), dp, (I.Null, I.Null), d) in
      let k'_, dupVars' =
        collectExp ((gs_, ss), I.Null, (p, s), k_, dupVars, true, d)
      in
      let epos = I.ctxLength k'_ in
      let apos = I.ctxLength dupVars' in
      let total = epos + apos in
      let epos', vars', g'_, eqn =
        abstractCtx ((gs_, ss), epos, I.Null, total, d, dp)
      in
      let posEA'', vars'', u'_, eqn' =
        abstractExp
          (true, (gs_, ss), (epos', total), vars', I.Null, total, d, (p, s), eqn)
      in
      let dAVars = makeAVarCtx (vars'', dupVars') in
      let dEVars = makeEVarCtx ((gs_, ss), vars'', I.Null, vars'', 0) in
      let s' = avarsToSub (dupVars', I.id) in
      let s'' = evarsToSub (vars'', s') in
      let g''_ = reverseCtx (g'_, I.Null) in
      begin if !TableParam.strengthen then
        let w' = Subordinate.weaken g''_ (I.targetFam u'_) in
        let iw = Whnf.invert w' in
        let gs' = Whnf.strengthen iw g''_ in
        (gs', dAVars, dEVars, u'_, eqn', s'')
      else (g''_, dAVars, dEVars, u'_, eqn', s'')
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
        let k_, _ =
          collectSub ((I.Null, I.id), I.Null, s, I.Null, I.Null, false, 0)
        in
        let epos = I.ctxLength k_ in
        let _, vars_, s' (*0 *) =
          abstractSub' (false, (I.Null, I.id), epos, I.Null, epos, s)
          (* total *)
        in
        let dEVars = makeEVarCtx ((I.Null, I.id), vars_, I.Null, vars_, 0) in
        let s1' = ctxToEVarSub (dEVars, I.id) in
        (dEVars, s')
  (* no linearization for answer substitution *)

  let raiseType g_ u_ = raiseType g_ u_
end
(*! sharing Conv.IntSyn = IntSyn' !*)
(*! structure TableParam : TABLEPARAM !*)
(*! sharing TableParam.IntSyn = IntSyn' !*)
(* functor AbstractTabled *)

(* # 1 "src/opsem/AbstractTabled.sml.ml" *)
