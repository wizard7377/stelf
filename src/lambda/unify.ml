(* # 1 "src/lambda/unify.sig.ml" *)
open! Basis
open Intsyn

(* Unification *)
(* Author: Frank Pfenning, Carsten Schuermann *)
module type UNIFY = sig
  (*! structure IntSyn : INTSYN !*)
  type nonrec unifTrail

  (* suspending and resuming trailing *)
  val suspend : unit -> unifTrail
  val resume : unifTrail -> unit

  (* trailing of variable instantiation *)
  val reset : unit -> unit
  val mark : unit -> unit
  val unwind : unit -> unit

  val instantiateEVar :
    IntSyn.exp option ref * IntSyn.exp * IntSyn.cnstr list -> unit

  val instantiateLVar : IntSyn.block option ref * IntSyn.block -> unit
  val resetAwakenCnstrs : unit -> unit
  val nextCnstr : unit -> IntSyn.cnstr option
  val addConstraint : IntSyn.cnstr list ref * IntSyn.cnstr -> unit
  val solveConstraint : IntSyn.cnstr -> unit
  val delay : IntSyn.eclo * IntSyn.cnstr -> unit

  (* unification *)
  val intersection : IntSyn.sub * IntSyn.sub -> IntSyn.sub

  exception Unify of string

  val unify : IntSyn.dctx * IntSyn.eclo * IntSyn.eclo -> unit

  (* raises Unify *)
  val unifyW : IntSyn.dctx * IntSyn.eclo * IntSyn.eclo -> unit

  (* raises Unify *)
  val unifyBlock : IntSyn.dctx * IntSyn.block * IntSyn.block -> unit

  (* raises Unify *)
  val unifySub : IntSyn.dctx * IntSyn.sub * IntSyn.sub -> unit

  (* raises Unify *)
  val invertible :
    IntSyn.dctx * IntSyn.eclo * IntSyn.sub * IntSyn.exp option ref -> bool

  val invertSub :
    IntSyn.dctx * IntSyn.sub * IntSyn.sub * IntSyn.exp option ref -> IntSyn.sub

  (* unifiable (G, Us,Us') will instantiate EVars as an effect *)
  val unifiable : IntSyn.dctx * IntSyn.eclo * IntSyn.eclo -> bool

  (* unifiable' (G, Us,Us') is like unifiable, but returns NONE for
     success and SOME(msg) for failure *)
  val unifiable' : IntSyn.dctx * IntSyn.eclo * IntSyn.eclo -> string option
end
(* signature UNIFY *)

(* # 1 "src/lambda/unify.fun.ml" *)
open! Whnf
open! Basis

(* Unification *)
(* Author: Frank Pfenning, Carsten Schuermann *)
(* Modified: Roberto Virga *)
module MakeUnify (Unify__0 : sig
  (*! structure IntSyn' : INTSYN !*)
  module Whnf : WHNF

  (*! sharing Whnf.IntSyn = IntSyn' !*)
  module Trail : TRAIL
end) : UNIFY = struct
  (*! structure IntSyn = IntSyn' !*)
  module Whnf = Unify__0.Whnf
  module Trail = Unify__0.Trail

  exception Unify of string
  exception NotInvertible

  type fAction =
    | BindExp of IntSyn.exp option ref * IntSyn.exp option
    | BindBlock of IntSyn.block option ref * IntSyn.block option
    | BindAdd of IntSyn.cnstr list ref * cAction list
    | FSolve of IntSyn.cnstr_ ref * IntSyn.cnstr_ * IntSyn.cnstr_

  and cAction = BindCnstr of IntSyn.cnstr_ ref * IntSyn.cnstr_

  type nonrec unifTrail = fAction Trail.trail

  open! struct
    open IntSyn

    type action =
      | Instantiate of exp option ref
      | InstantiateBlock of block option ref
      | Add of cnstr list ref
      | Solve of cnstr * cnstr_

    let globalTrail = (Trail.trail () : action Trail.trail)

    let rec copyCnstr = function
      | [] -> []
      | refC :: clist -> BindCnstr (refC, !refC) :: copyCnstr clist

    let rec copy = function
      | Instantiate refU -> BindExp (refU, !refU)
      | InstantiateBlock refB -> BindBlock (refB, !refB)
      | Add ({ contents = cnstrs_ } as cnstrs) ->
          BindAdd (cnstrs, copyCnstr !cnstrs)
      | Solve (cnstr, cnstr_) -> FSolve (cnstr, cnstr_, !cnstr)

    let rec resetCnstr = function
      | [] -> []
      | BindCnstr (refC, cnstr_) :: l_ -> begin
          refC := cnstr_;
          refC :: resetCnstr l_
        end

    let rec reset = function
      | BindExp (refU, u_) -> begin
          refU := u_;
          Instantiate refU
        end
      | BindBlock (refB, b_) -> begin
          refB := b_;
          InstantiateBlock refB
        end
      | BindAdd (cnstrs, cActions_) -> begin
          cnstrs := resetCnstr cActions_;
          Add cnstrs
        end
      | FSolve (refCnstr, cnstr_, cnstr'_) -> begin
          refCnstr := cnstr'_;
          Solve (refCnstr, cnstr_)
        end

    let rec suspend () = Trail.suspend (globalTrail, copy)
    let rec resume trail = Trail.resume (trail, globalTrail, reset)

    let rec undo = function
      | Instantiate refU -> refU := None
      | InstantiateBlock refB -> refB := None
      | Add ({ contents = cnstr :: cnstrL } as cnstrs) -> cnstrs := cnstrL
      | Solve (cnstr, cnstr_) -> cnstr := cnstr_

    let rec reset () = Trail.reset globalTrail
    let rec mark () = Trail.mark globalTrail
    let rec unwind () = Trail.unwind (globalTrail, undo)

    let rec addConstraint (cnstrs, cnstr) =
      begin
        cnstrs := cnstr :: !cnstrs;
        Trail.log (globalTrail, Add cnstrs)
      end

    let rec solveConstraint ({ contents = cnstr_ } as cnstr) =
      begin
        cnstr := Solved;
        Trail.log (globalTrail, Solve (cnstr, cnstr_))
      end

    let rec delayExpW = function
      | ((Uni l_ as u_), s1), _ -> ()
      | (Pi ((d_, p_), u_), s), cnstr -> begin
          delayDec ((d_, s), cnstr);
          delayExp ((u_, dot1 s), cnstr)
        end
      | (Root (h_, s_), s), cnstr -> begin
          delayHead (h_, cnstr);
          delaySpine ((s_, s), cnstr)
        end
      | (Lam (d_, u_), s), cnstr -> begin
          delayDec ((d_, s), cnstr);
          delayExp ((u_, dot1 s), cnstr)
        end
      | (EVar (g_, r, v_, cnstrs), s), cnstr -> addConstraint (cnstrs, cnstr)
      | (FgnExp (csfe_csid, csfe_ops), s), cnstr ->
          FgnExpStd.App.apply (csfe_csid, csfe_ops) (function u_ ->
              delayExp ((u_, s), cnstr))

    and delayExp (us_, cnstr) = delayExpW (Whnf.whnf us_, cnstr)

    and delayHead = function
      | FVar (x, v_, s'), cnstr -> delayExp ((v_, id), cnstr)
      | h_, _ -> ()

    and delaySpine = function
      | (Nil, s), cnstr -> ()
      | (App (u_, s_), s), cnstr -> begin
          delayExp ((u_, s), cnstr);
          delaySpine ((s_, s), cnstr)
        end
      | (SClo (s_, s'), s), cnstr -> delaySpine ((s_, comp (s', s)), cnstr)

    and delayDec ((Dec (name, v_), s), cnstr) = delayExp ((v_, s), cnstr)

    open! struct
      let awakenCnstrs = (ref [] : cnstr list ref)
    end

    let rec resetAwakenCnstrs () = awakenCnstrs := []

    let rec nextCnstr () =
      begin match !awakenCnstrs with
      | [] -> None
      | cnstr :: cnstrL -> begin
          awakenCnstrs := cnstrL;
          Some cnstr
        end
      end

    let rec instantiateEVar (refU, v_, cnstrL) =
      begin
        refU := Some v_;
        begin
          Trail.log (globalTrail, Instantiate refU);
          awakenCnstrs := cnstrL @ !awakenCnstrs
        end
      end

    let rec instantiateLVar (refB, b_) =
      begin
        refB := Some b_;
        Trail.log (globalTrail, InstantiateBlock refB)
      end

    let rec intersection = function
      | Dot (Idx k1, s1), Dot (Idx k2, s2) -> begin
          if k1 = k2 then dot1 (intersection (s1, s2))
          else comp (intersection (s1, s2), shift)
        end
      | (Dot _ as s1), Shift n2 ->
          intersection (s1, Dot (Idx (n2 + 1), Shift (n2 + 1)))
      | Shift n1, (Dot _ as s2) ->
          intersection (Dot (Idx (n1 + 1), Shift (n1 + 1)), s2)
      | Shift _, Shift _ -> id

    let rec weakenSub = function
      | g_, Shift n, ss -> begin
          if n < ctxLength g_ then
            weakenSub (g_, Dot (Idx (n + 1), Shift (n + 1)), ss)
          else id
        end
      | g_, Dot (Idx n, s'), ss -> begin
          match bvarSub (n, ss) with
          | Undef -> comp (weakenSub (g_, s', ss), shift)
          | Idx _ -> dot1 (weakenSub (g_, s', ss))
        end
      | g_, Dot (Undef, s'), ss -> comp (weakenSub (g_, s', ss), shift)

    let rec invertExp (g_, us_, ss, rOccur) =
      invertExpW (g_, Whnf.whnf us_, ss, rOccur)

    and invertExpW = function
      | g_, ((Uni _ as u_), s), _, _ -> u_
      | g_, (Pi ((d_, p_), v_), s), ss, rOccur ->
          Pi
            ( (invertDec (g_, (d_, s), ss, rOccur), p_),
              invertExp
                (Decl (g_, decSub (d_, s)), (v_, dot1 s), dot1 ss, rOccur) )
      | g_, (Lam (d_, v_), s), ss, rOccur ->
          Lam
            ( invertDec (g_, (d_, s), ss, rOccur),
              invertExp
                (Decl (g_, decSub (d_, s)), (v_, dot1 s), dot1 ss, rOccur) )
      | g_, (Root (h_, s_), s), ss, rOccur ->
          Root
            ( invertHead (g_, h_, ss, rOccur),
              invertSpine (g_, (s_, s), ss, rOccur) )
      | g_, ((EVar (r, gx_, v_, cnstrs) as x_), s), ss, rOccur -> begin
          if rOccur == r then raise NotInvertible
          else begin
            if Whnf.isPatSub s then
              let w = weakenSub (g_, s, ss) in
              begin if Whnf.isId w then EClo (x_, comp (s, ss))
              else raise NotInvertible
              end
            else EClo (x_, invertSub (g_, s, ss, rOccur))
          end
        end
      | g_, (FgnExp (csfe_csid, csfe_ops), s), ss, rOccur ->
          FgnExpStd.Map.apply (csfe_csid, csfe_ops) (function u_ ->
              invertExp (g_, (u_, s), ss, rOccur))

    and invertDec (g_, (Dec (name, v_), s), ss, rOccur) =
      Dec (name, invertExp (g_, (v_, s), ss, rOccur))

    and invertSpine = function
      | g_, (Nil, s), ss, rOccur -> Nil
      | g_, (App (u_, s_), s), ss, rOccur ->
          App
            ( invertExp (g_, (u_, s), ss, rOccur),
              invertSpine (g_, (s_, s), ss, rOccur) )
      | g_, (SClo (s_, s'), s), ss, rOccur ->
          invertSpine (g_, (s_, comp (s', s)), ss, rOccur)

    and invertHead = function
      | g_, BVar k, ss, rOccur -> begin
          match bvarSub (k, ss) with
          | Undef -> raise NotInvertible
          | Idx k' -> BVar k'
        end
      | g_, (Const _ as h_), ss, rOccur -> h_
      | g_, Proj ((Bidx k as b_), i), ss, rOccur -> begin
          match blockSub (b_, ss) with Bidx k' -> Proj (Bidx k', i)
        end
      | g_, (Proj (LVar (r, sk, (l, t)), i) as h_), ss, rOccur -> begin
          ignore (invertSub (g_, t, id, rOccur));
          h_
        end
      | g_, (Skonst _ as h_), ss, rOccur -> h_
      | g_, (Def _ as h_), ss, rOccur -> h_
      | g_, FVar (x, v_, s'), ss, rOccur -> begin
          ignore (invertExp (g_, (v_, id), id, rOccur));
          FVar (x, v_, comp (s', ss))
        end
      | g_, (FgnConst _ as h_), ss, rOccur -> h_

    and invertSub = function
      | g_, (Shift n as s), ss, rOccur -> begin
          if n < ctxLength g_ then
            invertSub (g_, Dot (Idx (n + 1), Shift (n + 1)), ss, rOccur)
          else comp (s, ss)
        end
      | g_, Dot (Idx n, s'), ss, rOccur -> begin
          match bvarSub (n, ss) with
          | Undef -> raise NotInvertible
          | ft_ -> Dot (ft_, invertSub (g_, s', ss, rOccur))
        end
      | g_, Dot (Exp u_, s'), ss, rOccur ->
          Dot
            ( Exp (invertExp (g_, (u_, id), ss, rOccur)),
              invertSub (g_, s', ss, rOccur) )

    let rec pruneExp (g_, us_, ss, rOccur) =
      pruneExpW (g_, Whnf.whnf us_, ss, rOccur)

    and pruneExpW = function
      | g_, ((Uni _ as u_), s), _, _ -> u_
      | g_, (Pi ((d_, p_), v_), s), ss, rOccur ->
          Pi
            ( (pruneDec (g_, (d_, s), ss, rOccur), p_),
              pruneExp (Decl (g_, decSub (d_, s)), (v_, dot1 s), dot1 ss, rOccur)
            )
      | g_, (Lam (d_, v_), s), ss, rOccur ->
          Lam
            ( pruneDec (g_, (d_, s), ss, rOccur),
              pruneExp (Decl (g_, decSub (d_, s)), (v_, dot1 s), dot1 ss, rOccur)
            )
      | g_, (Root (h_, s_), s), ss, rOccur ->
          Root
            ( pruneHead (g_, h_, ss, rOccur),
              pruneSpine (g_, (s_, s), ss, rOccur) )
      | g_, ((EVar (r, gx_, v_, cnstrs) as x_), s), ss, rOccur -> begin
          if rOccur == r then raise (Unify "Variable occurrence")
          else begin
            if Whnf.isPatSub s then
              let w = weakenSub (g_, s, ss) in
              begin if Whnf.isId w then EClo (x_, comp (s, ss))
              else
                let wi = Whnf.invert w in
                let v'_ = pruneExp (gx_, (v_, id), wi, rOccur) in
                let gy_ = pruneCtx (wi, gx_, rOccur) in
                let y_ = newEVar (gy_, v'_) in
                let yw_ = EClo (y_, w) in
                let _ = instantiateEVar (r, yw_, !cnstrs) in
                EClo (yw_, comp (s, ss))
              end
            else
              try EClo (x_, invertSub (g_, s, ss, rOccur))
              with NotInvertible ->
                let gy_ = pruneCtx (ss, g_, rOccur) in
                let v'_ = pruneExp (g_, (v_, s), ss, rOccur) in
                let y_ = newEVar (gy_, v'_) in
                let _ =
                  addConstraint
                    ( cnstrs,
                      ref (Eqn (g_, EClo (x_, s), EClo (y_, Whnf.invert ss))) )
                in
                y_
          end
        end
      | g_, (FgnExp (csfe_csid, csfe_ops), s), ss, rOccur ->
          FgnExpStd.Map.apply (csfe_csid, csfe_ops) (function u_ ->
              pruneExp (g_, (u_, s), ss, rOccur))
      | g_, ((AVar _ as x_), s), ss, rOccur -> raise (Unify "Left-over AVar")

    and pruneDec = function
      | g_, (Dec (name, v_), s), ss, rOccur ->
          Dec (name, pruneExp (g_, (v_, s), ss, rOccur))
      | g_, (NDec x, _), _, _ -> NDec x

    and pruneSpine = function
      | g_, (Nil, s), ss, rOccur -> Nil
      | g_, (App (u_, s_), s), ss, rOccur ->
          App
            ( pruneExp (g_, (u_, s), ss, rOccur),
              pruneSpine (g_, (s_, s), ss, rOccur) )
      | g_, (SClo (s_, s'), s), ss, rOccur ->
          pruneSpine (g_, (s_, comp (s', s)), ss, rOccur)

    and pruneHead = function
      | g_, BVar k, ss, rOccur -> begin
          match bvarSub (k, ss) with
          | Undef -> raise (Unify "Parameter dependency")
          | Idx k' -> BVar k'
        end
      | g_, (Const _ as h_), ss, rOccur -> h_
      | g_, Proj ((Bidx k as b_), i), ss, rOccur -> begin
          match blockSub (b_, ss) with Bidx k' -> Proj (Bidx k', i)
        end
      | g_, (Proj (LVar (r, sk, (l, t)), i) as h_), ss, rOccur -> begin
          ignore (pruneSub (g_, t, id, rOccur));
          h_
        end
      | g_, (Skonst _ as h_), ss, rOccur -> h_
      | g_, (Def _ as h_), ss, rOccur -> h_
      | g_, FVar (x, v_, s'), ss, rOccur -> begin
          ignore (pruneExp (g_, (v_, id), id, rOccur));
          FVar (x, v_, comp (s', ss))
        end
      | g_, (FgnConst _ as h_), ss, rOccur -> h_

    and pruneSub = function
      | g_, (Shift n as s), ss, rOccur ->
          if n < ctxLength g_ then
            pruneSub (g_, Dot (Idx (n + 1), Shift (n + 1)), ss, rOccur)
          else comp (s, ss)
      | g_, Dot (Idx n, s'), ss, rOccur -> begin
          match bvarSub (n, ss) with
          | Undef -> raise (Unify "Not prunable")
          | ft_ -> Dot (ft_, pruneSub (g_, s', ss, rOccur))
        end
      | g_, Dot (Exp u_, s'), ss, rOccur ->
          Dot
            ( Exp (pruneExp (g_, (u_, id), ss, rOccur)),
              pruneSub (g_, s', ss, rOccur) )

    and pruneCtx = function
      | Shift n, Null, rOccur -> Null
      | Dot (Idx k, t), Decl (g_, d_), rOccur ->
          let t' = comp (t, invShift) in
          let d'_ = pruneDec (g_, (d_, id), t', rOccur) in
          Decl (pruneCtx (t', g_, rOccur), d'_)
      | Dot (Undef, t), Decl (g_, d), rOccur -> pruneCtx (t, g_, rOccur)
      | Shift n, g_, rOccur ->
          pruneCtx (Dot (Idx (n + 1), Shift (n + 1)), g_, rOccur)

    let rec unifyExpW = function
      | g_, ((FgnExp (csfe1_csid, csfe1_ops), _) as us1_), us2_ -> begin
          match
            FgnExpStd.UnifyWith.apply (csfe1_csid, csfe1_ops)
              ( g_,
                let us2_e_, us2_s_ = us2_ in
                EClo (us2_e_, us2_s_) )
          with
          | Succeed residualL ->
              let rec execResidual = function
                | Assign (g_, EVar (r, _, _, cnstrs), w_, ss) ->
                    let w'_ = pruneExp (g_, (w_, id), ss, r) in
                    instantiateEVar (r, w'_, !cnstrs)
                | Delay (u_, cnstr) -> delayExp ((u_, id), cnstr)
              in
              List.app execResidual residualL
          | Fail -> raise (Unify "Foreign Expression Mismatch")
        end
      | g_, us1_, ((FgnExp (csfe2_csid, csfe2_ops), _) as us2_) -> begin
          match
            FgnExpStd.UnifyWith.apply (csfe2_csid, csfe2_ops)
              ( g_,
                let us1_e_, us1_s_ = us1_ in
                EClo (us1_e_, us1_s_) )
          with
          | Succeed opL ->
              let rec execOp = function
                | Assign (g_, EVar (r, _, _, cnstrs), w_, ss) ->
                    let w'_ = pruneExp (g_, (w_, id), ss, r) in
                    instantiateEVar (r, w'_, !cnstrs)
                | Delay (u_, cnstr) -> delayExp ((u_, id), cnstr)
              in
              List.app execOp opL
          | Fail -> raise (Unify "Foreign Expression Mismatch")
        end
      | g_, (Uni l1_, _), (Uni l2_, _) -> ()
      | g_, ((Root (h1_, s1_), s1) as us1_), ((Root (h2_, s2_), s2) as us2_) ->
        begin
          match (h1_, h2_) with
          | BVar k1, BVar k2 -> begin
              if k1 = k2 then unifySpine (g_, (s1_, s1), (s2_, s2))
              else raise (Unify "Bound variable clash")
            end
          | Const c1, Const c2 -> begin
              if c1 = c2 then unifySpine (g_, (s1_, s1), (s2_, s2))
              else raise (Unify "Constant clash")
            end
          | Proj (b1, i1), Proj (b2, i2) -> begin
              if i1 = i2 then begin
                unifyBlock (g_, b1, b2);
                unifySpine (g_, (s1_, s1), (s2_, s2))
              end
              else raise (Unify "Global parameter clash")
            end
          | Skonst c1, Skonst c2 -> begin
              if c1 = c2 then unifySpine (g_, (s1_, s1), (s2_, s2))
              else raise (Unify "Skolem constant clash")
            end
          | FVar (n1, _, _), FVar (n2, _, _) -> begin
              if n1 = n2 then unifySpine (g_, (s1_, s1), (s2_, s2))
              else raise (Unify "Free variable clash")
            end
          | Def d1, Def d2 -> begin
              if d1 = d2 then unifySpine (g_, (s1_, s1), (s2_, s2))
              else unifyDefDefW (g_, us1_, us2_)
            end
          | Def d1, Const c2 -> begin
              match defAncestor d1 with
              | Anc (_, _, None) -> unifyExpW (g_, Whnf.expandDef us1_, us2_)
              | Anc (_, _, Some c1) -> begin
                  if c1 = c2 then unifyExpW (g_, Whnf.expandDef us1_, us2_)
                  else raise (Unify "Constant clash")
                end
            end
          | Const c1, Def d2 -> begin
              match defAncestor d2 with
              | Anc (_, _, None) -> unifyExpW (g_, us1_, Whnf.expandDef us2_)
              | Anc (_, _, Some c2) -> begin
                  if c1 = c2 then unifyExpW (g_, us1_, Whnf.expandDef us2_)
                  else raise (Unify "Constant clash")
                end
            end
          | Def d1, BVar k2 -> raise (Unify "Head mismatch")
          | BVar k1, Def d2 -> raise (Unify "Head mismatch")
          | Def d1, _ -> unifyExpW (g_, Whnf.expandDef us1_, us2_)
          | _, Def d2 -> unifyExpW (g_, us1_, Whnf.expandDef us2_)
          | ( FgnConst (cs1, ConDec (n1, _, _, _, _, _)),
              FgnConst (cs2, ConDec (n2, _, _, _, _, _)) ) -> begin
              if cs1 = cs2 && n1 = n2 then ()
              else raise (Unify "Foreign Constant clash")
            end
          | ( FgnConst (cs1, ConDef (n1, _, _, w1_, _, _, _)),
              FgnConst (cs2, ConDef (n2, _, _, v_, w2_, _, _)) ) -> begin
              if cs1 = cs2 && n1 = n2 then ()
              else unifyExp (g_, (w1_, s1), (w2_, s2))
            end
          | FgnConst (_, ConDef (_, _, _, w1_, _, _, _)), _ ->
              unifyExp (g_, (w1_, s1), us2_)
          | _, FgnConst (_, ConDef (_, _, _, w2_, _, _, _)) ->
              unifyExp (g_, us1_, (w2_, s2))
          | _ -> raise (Unify "Head mismatch")
        end
      | g_, (Pi ((d1_, _), u1_), s1), (Pi ((d2_, _), u2_), s2) -> begin
          unifyDec (g_, (d1_, s1), (d2_, s2));
          unifyExp (Decl (g_, decSub (d1_, s1)), (u1_, dot1 s1), (u2_, dot1 s2))
        end
      | g_, ((Pi (_, _), _) as us1_), ((Root (Def _, _), _) as us2_) ->
          unifyExpW (g_, us1_, Whnf.expandDef us2_)
      | g_, ((Root (Def _, _), _) as us1_), ((Pi (_, _), _) as us2_) ->
          unifyExpW (g_, Whnf.expandDef us1_, us2_)
      | g_, (Lam (d1_, u1_), s1), (Lam (d2_, u2_), s2) ->
          unifyExp (Decl (g_, decSub (d1_, s1)), (u1_, dot1 s1), (u2_, dot1 s2))
      | g_, (Lam (d1_, u1_), s1), (u2_, s2) ->
          unifyExp
            ( Decl (g_, decSub (d1_, s1)),
              (u1_, dot1 s1),
              (Redex (EClo (u2_, shift), App (Root (BVar 1, Nil), Nil)), dot1 s2)
            )
      | g_, (u1_, s1), (Lam (d2_, u2_), s2) ->
          unifyExp
            ( Decl (g_, decSub (d2_, s2)),
              (Redex (EClo (u1_, shift), App (Root (BVar 1, Nil), Nil)), dot1 s1),
              (u2_, dot1 s2) )
      | ( g_,
          (((EVar (r1, g1_, v1_, cnstrs1) as u1_), s1) as us1_),
          (((EVar (r2, g2_, v2_, cnstrs2) as u2_), s2) as us2_) ) -> begin
          if r1 == r2 then begin
            if Whnf.isPatSub s1 then begin
              if Whnf.isPatSub s2 then
                let s' = intersection (s1, s2) in
                begin if Whnf.isId s' then ()
                else
                  let ss' = Whnf.invert s' in
                  let v1'_ = EClo (v1_, ss') in
                  let g1'_ = Whnf.strengthen (ss', g1_) in
                  instantiateEVar (r1, EClo (newEVar (g1'_, v1'_), s'), !cnstrs1)
                end
              else
                addConstraint
                  ( cnstrs2,
                    ref
                      (Eqn
                         ( g_,
                           (let us2_e_, us2_s_ = us2_ in
                            EClo (us2_e_, us2_s_)),
                           let us1_e_, us1_s_ = us1_ in
                           EClo (us1_e_, us1_s_) )) )
            end
            else
              addConstraint
                ( cnstrs1,
                  ref
                    (Eqn
                       ( g_,
                         (let us1_e_, us1_s_ = us1_ in
                          EClo (us1_e_, us1_s_)),
                         let us2_e_, us2_s_ = us2_ in
                         EClo (us2_e_, us2_s_) )) )
          end
          else begin
            if Whnf.isPatSub s1 then
              let ss1 = Whnf.invert s1 in
              let u2'_ = pruneExp (g_, us2_, ss1, r1) in
              instantiateEVar (r1, u2'_, !cnstrs1)
            else begin
              if Whnf.isPatSub s2 then
                let ss2 = Whnf.invert s2 in
                let u1'_ = pruneExp (g_, us1_, ss2, r2) in
                instantiateEVar (r2, u1'_, !cnstrs2)
              else
                let cnstr =
                  ref
                    (Eqn
                       ( g_,
                         (let us1_e_, us1_s_ = us1_ in
                          EClo (us1_e_, us1_s_)),
                         let us2_e_, us2_s_ = us2_ in
                         EClo (us2_e_, us2_s_) ))
                in
                addConstraint (cnstrs1, cnstr)
            end
          end
        end
      | g_, ((EVar (r, gx_, v_, cnstrs), s) as us1_), ((u2_, s2) as us2_) ->
        begin
          if Whnf.isPatSub s then
            let ss = Whnf.invert s in
            let u2'_ = pruneExp (g_, us2_, ss, r) in
            instantiateEVar (r, u2'_, !cnstrs)
          else
            addConstraint
              ( cnstrs,
                ref
                  (Eqn
                     ( g_,
                       (let us1_e_, us1_s_ = us1_ in
                        EClo (us1_e_, us1_s_)),
                       let us2_e_, us2_s_ = us2_ in
                       EClo (us2_e_, us2_s_) )) )
        end
      | g_, ((u1_, s1) as us1_), ((EVar (r, gx_, v_, cnstrs), s) as us2_) ->
        begin
          if Whnf.isPatSub s then
            let ss = Whnf.invert s in
            let u1'_ = pruneExp (g_, us1_, ss, r) in
            instantiateEVar (r, u1'_, !cnstrs)
          else
            addConstraint
              ( cnstrs,
                ref
                  (Eqn
                     ( g_,
                       (let us1_e_, us1_s_ = us1_ in
                        EClo (us1_e_, us1_s_)),
                       let us2_e_, us2_s_ = us2_ in
                       EClo (us2_e_, us2_s_) )) )
        end
      | g_, us1_, us2_ -> raise (Unify "Expression clash")

    and unifyExp (g_, ((e1_, s1) as us1_), ((e2_, s2) as us2_)) =
      unifyExpW (g_, Whnf.whnf us1_, Whnf.whnf us2_)

    and unifyDefDefW
        ( g_,
          ((Root (Def d1, s1_), s1) as us1_),
          ((Root (Def d2, s2_), s2) as us2_) ) =
      let (Anc (_, h1, c1Opt)) = defAncestor d1 in
      let (Anc (_, h2, c2Opt)) = defAncestor d2 in
      let _ =
        begin match (c1Opt, c2Opt) with
        | Some c1, Some c2 -> begin
            if c1 <> c2 then
              raise (Unify "Irreconcilable defined constant clash")
            else ()
          end
        | _ -> ()
        end
      in
      begin match Int.compare (h1, h2) with
      | Equal -> unifyExpW (g_, Whnf.expandDef us1_, Whnf.expandDef us2_)
      | Less -> unifyExpW (g_, us1_, Whnf.expandDef us2_)
      | Greater -> unifyExpW (g_, Whnf.expandDef us1_, us2_)
      end

    and unifySpine = function
      | g_, (Nil, _), (Nil, _) -> ()
      | g_, (SClo (s1_, s1'), s1), ss_ ->
          unifySpine (g_, (s1_, comp (s1', s1)), ss_)
      | g_, ss_, (SClo (s2_, s2'), s2) ->
          unifySpine (g_, ss_, (s2_, comp (s2', s2)))
      | g_, (App (u1_, s1_), s1), (App (u2_, s2_), s2) -> begin
          unifyExp (g_, (u1_, s1), (u2_, s2));
          unifySpine (g_, (s1_, s1), (s2_, s2))
        end

    and unifyDec (g_, (Dec (_, v1_), s1), (Dec (_, v2_), s2)) =
      unifyExp (g_, (v1_, s1), (v2_, s2))

    and unifySub = function
      | g_, Shift n1, Shift n2 -> ()
      | g_, Shift n, (Dot _ as s2) ->
          unifySub (g_, Dot (Idx (n + 1), Shift (n + 1)), s2)
      | g_, (Dot _ as s1), Shift m ->
          unifySub (g_, s1, Dot (Idx (m + 1), Shift (m + 1)))
      | g_, Dot (ft1_, s1), Dot (ft2_, s2) -> begin
          begin match (ft1_, ft2_) with
          | Idx n1, Idx n2 -> begin
              if n1 <> n2 then raise (Error "SOME variables mismatch") else ()
            end
          | Exp u1_, Exp u2_ -> unifyExp (g_, (u1_, id), (u2_, id))
          | Exp u1_, Idx n2 ->
              unifyExp (g_, (u1_, id), (Root (BVar n2, Nil), id))
          | Idx n1, Exp u2_ ->
              unifyExp (g_, (Root (BVar n1, Nil), id), (u2_, id))
          end;
          unifySub (g_, s1, s2)
        end

    and unifyBlock = function
      | g_, LVar ({ contents = Some b1_ }, s, _), b2_ ->
          unifyBlock (g_, blockSub (b1_, s), b2_)
      | g_, b1_, LVar ({ contents = Some b2_ }, s, _) ->
          unifyBlock (g_, b1_, blockSub (b2_, s))
      | g_, b1_, b2_ -> unifyBlockW (g_, b1_, b2_)

    and unifyBlockW = function
      | ( g_,
          LVar (r1, (Shift k1 as s1), (l1, t1)),
          LVar (r2, (Shift k2 as s2), (l2, t2)) ) -> begin
          if l1 <> l2 then raise (Unify "Label clash")
          else begin
            if r1 == r2 then ()
            else begin
              unifySub (g_, comp (t1, s1), comp (t2, s2));
              begin if k1 < k2 then
                instantiateLVar (r1, LVar (r2, Shift (k2 - k1), (l2, t2)))
              else instantiateLVar (r2, LVar (r1, Shift (k1 - k2), (l1, t1)))
              end
            end
          end
        end
      | g_, LVar (r1, s1, (l1, t1)), b2_ ->
          instantiateLVar (r1, blockSub (b2_, Whnf.invert s1))
      | g_, b1_, LVar (r2, s2, (l2, t2)) ->
          instantiateLVar (r2, blockSub (b1_, Whnf.invert s2))
      | g_, Bidx n1, Bidx n2 -> begin
          if n1 <> n2 then raise (Unify "Block index clash") else ()
        end

    let rec unify1W (g_, us1_, us2_) =
      begin
        unifyExpW (g_, us1_, us2_);
        awakeCnstr (nextCnstr ())
      end

    and unify1 (g_, us1_, us2_) =
      begin
        unifyExp (g_, us1_, us2_);
        awakeCnstr (nextCnstr ())
      end

    and awakeCnstr = function
      | None -> ()
      | Some { contents = Solved } -> awakeCnstr (nextCnstr ())
      | Some ({ contents = Eqn (g_, u1_, u2_) } as cnstr) -> begin
          solveConstraint cnstr;
          unify1 (g_, (u1_, id), (u2_, id))
        end
      | Some { contents = FgnCnstr (csfc_csid, csfc_ops) } -> begin
          if FgnCnstrStd.Awake.apply (csfc_csid, csfc_ops) () then ()
          else raise (Unify "Foreign constraint violated")
        end

    let rec unifyW (g_, us1_, us2_) =
      begin
        resetAwakenCnstrs ();
        unify1W (g_, us1_, us2_)
      end

    let rec unify (g_, us1_, us2_) =
      begin
        resetAwakenCnstrs ();
        unify1 (g_, us1_, us2_)
      end
  end

  (* ? *)
  (* Associate a constraint to an expression *)
  (* delayExpW ((U, s), cnstr) = ()

       Invariant:
       If   G' |- s : G    G |- U : V    (U,s)  in whnf
       then
       the constraint cnstr is added to all the rigid EVar occurrences in U[s]
    *)
  (* s = id *)
  (* no other cases by invariant *)
  (* delayExp ((U, s), cnstr) = ()
       as in delayExpCW, except that the argument may not be in whnf
    *)
  (* delayHead (H, s, rOccur) = ()

       Invariant:
       If   G' |- H : V
       and  G' |- s : G         s is a pattern substitution
       then
       the constraint cnstr is added to a total of n rigid EVar occurrences in H[s]
    *)
  (* delaySpine ((S, s), cnstr) = ()

       Invariant:
       If   G' |- s : G    G |- S : V > W
       then      G  |- S' : V' > W'
       the constraint cnstr is added to all the rigid EVar occurrences in S[s]
    *)
  (* delayDec see delayExp *)
  (* Instantiating EVars  *)
  (* Instantiating LVars  *)
  (* local *)
  (* intersection (s1, s2) = s'
       s' = s1 /\ s2 (see JICSLP'96)

       Invariant:
       If   G |- s1 : G'    s1 patsub
       and  G |- s2 : G'    s2 patsub
       then G |- s' : G'' for some G''
       and  s' patsub
    *)
  (* both substitutions are the same number of shifts by invariant *)
  (* all other cases impossible for pattern substitutions *)
  (* weakenSub (G1, s, ss) = w'

       Invariant:
       If    G |- s : G1        s patsub 
       and   G2 |- ss : G       ss strsub 
       then  G1 |- w' : G1'     w' weaksub 

       and   G2 |- w' o s o ss : G1'  is fully defined
       and   G1' is maximal such
    *)
  (* no other cases, ss is strsub *)
  (* invert (G, (U, s), ss, rOccur) = U[s][ss]

       G |- s : G'   G' |- U : V  (G |- U[s] : V[s])
       G'' |- ss : G

       Effect: raises NotInvertible if U[s][ss] does not exist
               or rOccurs occurs in U[s]
               does NOT prune EVars in U[s] according to ss; fails instead
    *)
  (* = id *)
  (* s not patsub *)
  (* invertExp may raise NotInvertible *)
  (* other cases impossible since (U,s1) whnf *)
  (* blockSub (B, ss) should always be defined *)
  (* Fri Dec 28 10:03:12 2001 -fp !!! *)
  (* claim: LVar does not need to be pruned since . |- t : Gsome *)
  (* so we perform only the occurs-check here as for FVars *)
  (* Sat Dec  8 13:39:41 2001 -fp !!! *)
  (* this is not true any more, Sun Dec  1 11:28:47 2002 -cs  *)
  (* Changed from Null to G Sat Dec  7 21:58:00 2002 -fp *)
  (* V does not to be pruned, since . |- V : type and s' = ^k *)
  (* perform occurs-check for r only *)
  (* why G here? -fp !!! *)
  (* pruneSub never allows pruning OUTDATED *)
  (* in the presence of block variables, this invariant
       doesn't hold any more, because substitutions do not
       only occur in EVars any more but also in LVars!
       and there pruning is allowed!   Tue May 29 21:50:17 EDT 2001 -cs *)
  (* must be defined *)
  (* below my raise NotInvertible *)
  (* pruneSub (G, Dot (Undef, s), ss, rOccur) is impossible *)
  (* By invariant, all EVars X[s] are such that s is defined everywhere *)
  (* Pruning establishes and maintains this invariant *)
  (* invertCtx does not appear to be necessary *)
  (*
    and invertCtx (Shift n, Null, rOccur) = Null
      | invertCtx (Dot (Idx k, t), Decl (G, D), rOccur) =
        let
          val t' = comp (t, invShift)
          val D' = invertDec (G, (D, id), t', rOccur)
        in
          Decl (invertCtx (t', G, rOccur), D')
        end
      | invertCtx (Dot (Undef, t), Decl (G, d), rOccur) =
          invertCtx (t, G, rOccur)
      | invertCtx (Shift n, G, rOccur) =
          invertCtx (Dot (Idx (n+1), Shift (n+1)), G, rOccur)
    *)
  (* prune (G, (U, s), ss, rOccur) = U[s][ss]

       !!! looks wrong to me -kw
       G |- U : V    G' |- s : G  (G' |- U[s] : V[s])
       G'' |- ss : G'
       !!! i would say
       G |- s : G'   G' |- U : V  (G  |- U[s] : V[s])
       G'' |- ss : G

       Effect: prunes EVars in U[s] according to ss
               raises Unify if U[s][ss] does not exist, or rOccur occurs in U[s]
    *)
  (* = id *)
  (* val V' = EClo (V, wi) *)
  (* val GY = Whnf.strengthen (wi, GX) *)
  (* shortcut on GY possible by invariant on GX and V[s]? -fp *)
  (* could optimize by checking for identity subst *)
  (* s not patsub *)
  (* val GY = Whnf.strengthen (ss, G) *)
  (* shortcuts possible by invariants on G? *)
  (* prune or invert??? *)
  (* val V' = EClo (V, comp (s, ss)) *)
  (* prune or invert??? *)
  (* this case should never happen! *)
  (* other cases impossible since (U,s1) whnf *)
  (* Added for the meta level -cs Tue Aug 17 17:09:27 2004 *)
  (* blockSub (B, ss) should always be defined *)
  (* Fri Dec 28 10:03:12 2001 -fp !!! *)
  (* claim: LVar does not need to be pruned since . |- t : Gsome *)
  (* so we perform only the occurs-check here as for FVars *)
  (* Sat Dec  8 13:39:41 2001 -fp !!! *)
  (* this is not true any more, Sun Dec  1 11:28:47 2002 -cs  *)
  (* Changed from Null to G Sat Dec  7 21:58:00 2002 -fp *)
  (* V does not to be pruned, since . |- V : type and s' = ^k *)
  (* perform occurs-check for r only *)
  (* why G here? -fp !!! *)
  (* pruneSub never allows pruning OUTDATED *)
  (* in the presence of block variables, this invariant
       doesn't hold any more, because substitutions do not
       only occur in EVars any more but also in LVars!
       and there pruning is allowed!   Tue May 29 21:50:17 EDT 2001 -cs *)
  (* must be defined *)
  (* below my raise Unify *)
  (* pruneSub (G, Dot (Undef, s), ss, rOccur) is impossible *)
  (* By invariant, all EVars X[s] are such that s is defined everywhere *)
  (* Pruning establishes and maintains this invariant *)
  (* unifyExpW (G, (U1, s1), (U2, s2)) = ()

       Invariant:
       If   G |- s1 : G1   G1 |- U1 : V1    (U1,s1) in whnf
       and  G |- s2 : G2   G2 |- U2 : V2    (U2,s2) in whnf
       and  G |- V1 [s1] = V2 [s2]  : L    (for some level L)
        ***** or V1 = V2 = kind  (needed to check type definitions)
        ***** added by kw Apr 5 2002
       and  s1, U1, s2, U2 do not contain any blockvariable indices Bidx
       then if   there is an instantiation I :
                 s.t. G |- U1 [s1] <I> == U2 [s2] <I>
            then instantiation is applied as effect, () returned
            else exception Unify is raised
       Other effects: EVars may be lowered
                      constraints may be added for non-patterns
    *)
  (* L1 = L2 = type, by invariant *)
  (* unifyUni (L1, L2) - removed Mon Aug 24 12:18:24 1998 -fp *)
  (* s1 = s2 = id by whnf *)
  (* order of calls critical to establish unifySpine invariant *)
  (* because of strict *)
  (*  unifyExpW (G, Whnf.expandDef (Us1), Whnf.expandDef (Us2)) *)
  (* four new cases for defined constants *)
  (* conservative *)
  (* conservative *)
  (* due to strictness! *)
  (* due to strictness! *)
  (* next two cases for def/fgn, fgn/def *)
  (* we require unique string representation of external constants *)
  (* D1[s1] = D2[s2]  by invariant *)
  (* ETA: can't occur if eta expanded *)
  (* for rhs:  (U2[s2])[^] 1 = U2 [s2 o ^] 1 = U2 [^ o (1. s2 o ^)] 1
                        = (U2 [^] 1) [1.s2 o ^] *)
  (* Cannot occur if expressions are eta expanded *)
  (* same reasoning holds as above *)
  (* postpone, if s1 or s2 are not patsub *)
  (* compute ss' directly? *)
  (* without the next optimization, bugs/hangs/sources.cfg
                     would gets into an apparent infinite loop
                     Fri Sep  5 20:23:27 2003 -fp
                  *)
  (* added for definitions Mon Sep  1 19:53:13 2003 -fp *)
  (* X[s] = X[s] *)
  (* invertExp ((V1, id), s', ref NONE) *)
  (* instantiateEVar (r1, EClo (U2, comp(s2, ss1)), !cnstrs1) *)
  (* invertExpW (Us2, s1, ref NONE) *)
  (* instantiateEVar (r2, EClo (U1, comp(s1, ss2)), !cnstr2) *)
  (* invertExpW (Us1, s2, ref NONE) *)
  (* instantiateEVar (r, EClo (U2, comp(s2, ss)), !cnstrs) *)
  (* invertExpW (Us2, s, r) *)
  (* instantiateEVar (r, EClo (U1, comp(s1, ss)), !cnstrs) *)
  (* invertExpW (Us1, s, r) *)
  (* covers most remaining cases *)
  (* the cases for EClo or Redex should not occur because of whnf invariant *)
  (* unifyExp (G, (U1, s1), (U2, s2)) = ()
       as in unifyExpW, except that arguments may not be in whnf
    *)
  (*  unifyExpW (G, Whnf.expandDef (Us1), Whnf.expandDef (Us2)) *)
  (* conservative *)
  (* unifySpine (G, (S1, s1), (S2, s2)) = ()

       Invariant:
       If   G |- s1 : G1   G1 |- S1 : V1 > W1
       and  G |- s2 : G2   G2 |- S2 : V2 > W2
       and  G |- V1 [s1] = V2 [s2]  : L    (for some level L)
       and  G |- W1 [s1] = W2 [s2]
       then if   there is an instantiation I :
                 s.t. G |- S1 [s1] <I> == S2 [s2] <I>
            then instantiation is applied as effect, () returned
            else exception Unify is raised
       Other effects: EVars may be lowered,
                      constraints may be added for non-patterns
    *)
  (* Nil/App or App/Nil cannot occur by typing invariants *)
  (* unifySub (G, s1, s2) = ()

       Invariant:
       If   G |- s1 : G'
       and  G |- s2 : G'
       then unifySub (G, s1, s2) terminates with ()
            iff there exists an instantiation I, such that
            s1 [I] = s2 [I]

       Remark:  unifySub is used only to unify the instantiation of SOME variables
    *)
  (* conjecture: G == Null at all times *)
  (* Thu Dec  6 21:01:09 2001 -fp *)
  (* by invariant *)
  (*         | (Undef, Undef) =>
           | _ => false *)
  (* not possible because of invariant? -cs *)
  (* substitutions s1 and s2 were redundant here --- removed *)
  (* Sat Dec  8 11:47:12 2001 -fp !!! *)
  (* Sat Dec  7 22:04:31 2002 -fp *)
  (* was: unifySub (G, t1, t2)  Jul 22 2010 *)
  (* -- ABP *)
  (* -- ABP *)
  (*      | unifyBlockW (G, LVar (r1, Shift(k1), (l1, t1)), Bidx i2) =
            (r1 := SOME (Bidx (i2 -k1)) ; ())  -- ABP 

      | unifyBlockW (G, Bidx i1, LVar (r2, Shift(k2), (l2, t2))) =
            (r2 := SOME (Bidx (i1 -k2)) ; ())  -- ABP 
*)
  (* How can the next case arise? *)
  (* Sat Dec  8 11:49:16 2001 -fp !!! *)
  (*
      | unifyBlock (LVar (r1, _, _), B as Bidx _) = instantiate (r1, B)
      | unifyBlock (B as Bidx _, LVar (r2, _, _)) =

      This is still difficult --- B must make sense in the context of the LVar
      Shall we use the inverse of a pattern substitution? Or postpone as
      a constraint if pattern substitution does not exist?
      Sun Dec  1 11:33:13 2002 -cs

*)
  (* unifTrail already declared at struct level *)
  let reset = reset
  let mark = mark
  let unwind = unwind
  let suspend = suspend
  let resume = resume
  let delay = delayExp
  let instantiateEVar = instantiateEVar
  let instantiateLVar = instantiateLVar
  let resetAwakenCnstrs = resetAwakenCnstrs
  let nextCnstr = nextCnstr
  let addConstraint = addConstraint
  let solveConstraint = solveConstraint
  let intersection = intersection
  let unifyW = unifyW
  let unify = unify
  let unifySub = unifySub
  let unifyBlock = unifyBlock

  let rec invertible (g_, us_, ss, rOccur) =
    try
      begin
        ignore (invertExp (g_, us_, ss, rOccur));
        true
      end
    with NotInvertible -> false

  let invertSub = invertSub

  let rec unifiable (g_, us1_, us2_) =
    try
      begin
        unify (g_, us1_, us2_);
        true
      end
    with Unify msg -> false

  let rec unifiable' (g_, us1_, us2_) =
    try
      begin
        unify (g_, us1_, us2_);
        None
      end
    with Unify msg -> Some msg
end
(* functor Unify *)

(* # 1 "src/lambda/unify.sml.ml" *)
