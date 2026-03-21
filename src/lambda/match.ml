(* # 1 "src/lambda/match.sig.ml" *)
open! Basis
open Intsyn

(* Matching *)
(* Author: Frank Pfenning, Carsten Schuermann *)
module type MATCH = sig
  (*! structure IntSyn : INTSYN !*)
  (* matching *)
  exception Match of string

  val match_ : IntSyn.dctx * IntSyn.eclo * IntSyn.eclo -> unit

  (* raises Unify *)
  val matchW : IntSyn.dctx * IntSyn.eclo * IntSyn.eclo -> unit

  (* raises Unify *)
  val matchBlock : IntSyn.dctx * IntSyn.block * IntSyn.block -> unit

  (* raises Unify *)
  val matchSub : IntSyn.dctx * IntSyn.sub * IntSyn.sub -> unit

  (* raises Unify *)
  (* instance (G, Us,Us') will instantiate EVars as an effect 
     checks if Us' is an instance of Us *)
  val instance : IntSyn.dctx * IntSyn.eclo * IntSyn.eclo -> bool

  (* instance' (G, Us,Us') is like instance, but returns NONE for
     success and SOME(msg) for failure *)
  val instance' : IntSyn.dctx * IntSyn.eclo * IntSyn.eclo -> string option
end
(* signature MATCH *)

(* # 1 "src/lambda/match.fun.ml" *)
open! Whnf
open! Unify
open! Basis

(* Matching *)
(* Unification modified to Matching *)
(* Author: Frank Pfenning, Carsten Schuermann *)
(* Modified: Roberto Virga, Brigitte Pientka *)
module MakeMatch (Match__0 : sig
  (*! structure IntSyn' : INTSYN !*)
  module Whnf : WHNF

  (*! sharing Whnf.IntSyn = IntSyn' !*)
  module Unify : UNIFY
  module Trail : TRAIL
end) : MATCH = struct
  (*! structure IntSyn = IntSyn' !*)
  module Whnf = Match__0.Whnf
  module Unify = Match__0.Unify
  module Trail = Match__0.Trail

  exception Match of string
  exception NotInvertible

  open! struct
    open IntSyn

    let delayExp = Unify.delay

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
          if rOccur == r then raise (Match "Variable occurrence")
          else begin
            if Whnf.isPatSub s then
              let w = weakenSub (g_, s, ss) in
              begin if Whnf.isId w then EClo (x_, comp (s, ss))
              else
                raise
                  (Match "Invertible Substitution does not necessarily exist\n")
              end
            else
              try EClo (x_, Unify.invertSub (g_, s, ss, rOccur))
              with NotInvertible ->
                let gy_ = pruneCtx (ss, g_, rOccur) in
                let v'_ = pruneExp (g_, (v_, s), ss, rOccur) in
                let y_ = newEVar (gy_, v'_) in
                let _ =
                  Unify.addConstraint
                    ( cnstrs,
                      ref (Eqn (g_, EClo (x_, s), EClo (y_, Whnf.invert ss))) )
                in
                y_
          end
        end
      | g_, (FgnExp (csfe_csid, csfe_ops), s), ss, rOccur ->
          FgnExpStd.Map.apply (csfe_csid, csfe_ops) (function u_ ->
              pruneExp (g_, (u_, s), ss, rOccur))
      | g_, ((AVar _ as x_), s), ss, rOccur -> raise (Match "Left-over AVar")

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
          | Undef -> raise (Match "Parameter dependency")
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
      | g_, (Shift n as s), ss, rOccur -> begin
          if n < ctxLength g_ then
            pruneSub (g_, Dot (Idx (n + 1), Shift (n + 1)), ss, rOccur)
          else comp (s, ss)
        end
      | g_, Dot (Idx n, s'), ss, rOccur -> begin
          match bvarSub (n, ss) with
          | Undef -> raise (Match "Not prunable")
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

    let rec matchExpW = function
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
                    Unify.instantiateEVar (r, w'_, !cnstrs)
                | Delay (u_, cnstr) -> delayExp ((u_, id), cnstr)
              in
              List.app execResidual residualL
          | Fail -> raise (Match "Foreign Expression Mismatch")
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
                    Unify.instantiateEVar (r, w'_, !cnstrs)
                | Delay (u_, cnstr) -> delayExp ((u_, id), cnstr)
              in
              List.app execOp opL
          | Fail -> raise (Match "Foreign Expression Mismatch")
        end
      | g_, (Uni l1_, _), (Uni l2_, _) -> ()
      | g_, ((Root (h1_, s1_), s1) as us1_), ((Root (h2_, s2_), s2) as us2_) ->
        begin
          match (h1_, h2_) with
          | BVar k1, BVar k2 -> begin
              if k1 = k2 then matchSpine (g_, (s1_, s1), (s2_, s2))
              else raise (Match "Bound variable clash")
            end
          | Const c1, Const c2 -> begin
              if c1 = c2 then matchSpine (g_, (s1_, s1), (s2_, s2))
              else raise (Match "Constant clash")
            end
          | Proj (b1, i1), Proj (b2, i2) -> begin
              if i1 = i2 then begin
                matchBlock (g_, b1, b2);
                matchSpine (g_, (s1_, s1), (s2_, s2))
              end
              else raise (Match "Global parameter clash")
            end
          | Skonst c1, Skonst c2 -> begin
              if c1 = c2 then matchSpine (g_, (s1_, s1), (s2_, s2))
              else raise (Match "Skolem constant clash")
            end
          | FVar (n1, _, _), FVar (n2, _, _) -> begin
              if n1 = n2 then matchSpine (g_, (s1_, s1), (s2_, s2))
              else raise (Match "Free variable clash")
            end
          | Def d1, Def d2 -> begin
              if d1 = d2 then matchSpine (g_, (s1_, s1), (s2_, s2))
              else matchDefDefW (g_, us1_, us2_)
            end
          | Def d1, Const c2 -> begin
              match defAncestor d1 with
              | Anc (_, _, None) -> matchExpW (g_, Whnf.expandDef us1_, us2_)
              | Anc (_, _, Some c1) -> begin
                  if c1 = c2 then matchExpW (g_, Whnf.expandDef us1_, us2_)
                  else raise (Match "Constant clash")
                end
            end
          | Const c1, Def d2 -> begin
              match defAncestor d2 with
              | Anc (_, _, None) -> matchExpW (g_, us1_, Whnf.expandDef us2_)
              | Anc (_, _, Some c2) -> begin
                  if c1 = c2 then matchExpW (g_, us1_, Whnf.expandDef us2_)
                  else raise (Match "Constant clash")
                end
            end
          | Def d1, BVar k2 -> raise (Match "Head mismatch")
          | BVar k1, Def d2 -> raise (Match "Head mismatch")
          | Def d1, _ -> matchExpW (g_, Whnf.expandDef us1_, us2_)
          | _, Def d2 -> matchExpW (g_, us1_, Whnf.expandDef us2_)
          | ( FgnConst (cs1, ConDec (n1, _, _, _, _, _)),
              FgnConst (cs2, ConDec (n2, _, _, _, _, _)) ) -> begin
              if cs1 = cs2 && n1 = n2 then ()
              else raise (Match "Foreign Constant clash")
            end
          | ( FgnConst (cs1, ConDef (n1, _, _, w1_, _, _, _)),
              FgnConst (cs2, ConDef (n2, _, _, v_, w2_, _, _)) ) -> begin
              if cs1 = cs2 && n1 = n2 then ()
              else matchExp (g_, (w1_, s1), (w2_, s2))
            end
          | FgnConst (_, ConDef (_, _, _, w1_, _, _, _)), _ ->
              matchExp (g_, (w1_, s1), us2_)
          | _, FgnConst (_, ConDef (_, _, _, w2_, _, _, _)) ->
              matchExp (g_, us1_, (w2_, s2))
          | _ -> raise (Match "Head mismatch")
        end
      | g_, (Pi ((d1_, _), u1_), s1), (Pi ((d2_, _), u2_), s2) -> begin
          matchDec (g_, (d1_, s1), (d2_, s2));
          matchExp (Decl (g_, decSub (d1_, s1)), (u1_, dot1 s1), (u2_, dot1 s2))
        end
      | g_, ((Pi (_, _), _) as us1_), ((Root (Def _, _), _) as us2_) ->
          matchExpW (g_, us1_, Whnf.expandDef us2_)
      | g_, ((Root (Def _, _), _) as us1_), ((Pi (_, _), _) as us2_) ->
          matchExpW (g_, Whnf.expandDef us1_, us2_)
      | g_, (Lam (d1_, u1_), s1), (Lam (d2_, u2_), s2) ->
          matchExp (Decl (g_, decSub (d1_, s1)), (u1_, dot1 s1), (u2_, dot1 s2))
      | g_, (Lam (d1_, u1_), s1), (u2_, s2) ->
          matchExp
            ( Decl (g_, decSub (d1_, s1)),
              (u1_, dot1 s1),
              (Redex (EClo (u2_, shift), App (Root (BVar 1, Nil), Nil)), dot1 s2)
            )
      | g_, (u1_, s1), (Lam (d2_, u2_), s2) ->
          matchExp
            ( Decl (g_, decSub (d2_, s2)),
              (Redex (EClo (u1_, shift), App (Root (BVar 1, Nil), Nil)), dot1 s1),
              (u2_, dot1 s2) )
      | g_, ((EVar (r, gx_, v_, cnstrs), s) as us1_), ((u2_, s2) as us2_) ->
        begin
          if Whnf.isPatSub s then
            let ss = Whnf.invert s in
            let u2'_ = pruneExp (g_, us2_, ss, r) in
            Unify.instantiateEVar (r, u2'_, !cnstrs)
          else
            Unify.addConstraint
              ( cnstrs,
                ref
                  (Eqn
                     ( g_,
                       (let us1_e_, us1_s_ = us1_ in
                        EClo (us1_e_, us1_s_)),
                       let us2_e_, us2_s_ = us2_ in
                       EClo (us2_e_, us2_s_) )) )
        end
      | g_, us1_, us2_ -> raise (Match "Expression clash")

    and matchExp (g_, ((e1_, s1) as us1_), ((e2_, s2) as us2_)) =
      matchExpW (g_, Whnf.whnf us1_, Whnf.whnf us2_)

    and matchDefDefW
        ( g_,
          ((Root (Def d1, s1_), s1) as us1_),
          ((Root (Def d2, s2_), s2) as us2_) ) =
      let (Anc (_, h1, c1Opt)) = defAncestor d1 in
      let (Anc (_, h2, c2Opt)) = defAncestor d2 in
      let _ =
        begin match (c1Opt, c2Opt) with
        | Some c1, Some c2 -> begin
            if c1 <> c2 then
              raise (Match "Irreconcilable defined constant clash")
            else ()
          end
        | _ -> ()
        end
      in
      begin match Int.compare (h1, h2) with
      | Equal -> matchExpW (g_, Whnf.expandDef us1_, Whnf.expandDef us2_)
      | Less -> matchExpW (g_, us1_, Whnf.expandDef us2_)
      | Greater -> matchExpW (g_, Whnf.expandDef us1_, us2_)
      end

    and matchSpine = function
      | g_, (Nil, _), (Nil, _) -> ()
      | g_, (SClo (s1_, s1'), s1), ss_ ->
          matchSpine (g_, (s1_, comp (s1', s1)), ss_)
      | g_, ss_, (SClo (s2_, s2'), s2) ->
          matchSpine (g_, ss_, (s2_, comp (s2', s2)))
      | g_, (App (u1_, s1_), s1), (App (u2_, s2_), s2) -> begin
          matchExp (g_, (u1_, s1), (u2_, s2));
          matchSpine (g_, (s1_, s1), (s2_, s2))
        end

    and matchDec (g_, (Dec (_, v1_), s1), (Dec (_, v2_), s2)) =
      matchExp (g_, (v1_, s1), (v2_, s2))

    and matchSub = function
      | g_, Shift n1, Shift n2 -> ()
      | g_, Shift n, (Dot _ as s2) ->
          matchSub (g_, Dot (Idx (n + 1), Shift (n + 1)), s2)
      | g_, (Dot _ as s1), Shift m ->
          matchSub (g_, s1, Dot (Idx (m + 1), Shift (m + 1)))
      | g_, Dot (ft1_, s1), Dot (ft2_, s2) -> begin
          begin match (ft1_, ft2_) with
          | Idx n1, Idx n2 -> begin
              if n1 <> n2 then raise (Error "SOME variables mismatch") else ()
            end
          | Exp u1_, Exp u2_ -> matchExp (g_, (u1_, id), (u2_, id))
          | Exp u1_, Idx n2 ->
              matchExp (g_, (u1_, id), (Root (BVar n2, Nil), id))
          | Idx n1, Exp u2_ ->
              matchExp (g_, (Root (BVar n1, Nil), id), (u2_, id))
          end;
          matchSub (g_, s1, s2)
        end

    and matchBlock = function
      | g_, LVar ({ contents = Some b1_ }, s, _), b2_ ->
          matchBlock (g_, blockSub (b1_, s), b2_)
      | g_, b1_, LVar ({ contents = Some b2_ }, s, _) ->
          matchBlock (g_, b1_, blockSub (b2_, s))
      | g_, b1_, b2_ -> matchBlockW (g_, b1_, b2_)

    and matchBlockW = function
      | g_, LVar (r1, Shift k1, (l1, t1)), LVar (r2, Shift k2, (l2, t2)) ->
        begin
          if l1 <> l2 then raise (Match "Label clash")
          else begin
            if r1 == r2 then ()
            else begin
              matchSub (g_, t1, t2);
              begin
                begin if k1 <> k2 then raise Bind else ()
                end;
                let ss = Whnf.invert (Shift k1) in
                let t2' = pruneSub (g_, t2, ss, ref None) in
                Unify.instantiateLVar (r1, LVar (r2, Shift 0, (l2, t2')))
              end
            end
          end
        end
      | g_, LVar (r1, s1, (l1, t1)), b2_ -> begin
          r1 := Some (blockSub (b2_, Whnf.invert s1));
          ()
        end
      | g_, b1_, LVar (r2, s2, (l2, t2)) -> begin
          r2 := Some (blockSub (b1_, Whnf.invert s2));
          ()
        end
      | g_, Bidx n1, Bidx n2 -> begin
          if n1 <> n2 then raise (Match "Block index clash") else ()
        end

    let rec match1W (g_, us1_, us2_) =
      begin
        matchExpW (g_, us1_, us2_);
        awakeCnstr (Unify.nextCnstr ())
      end

    and match1 (g_, us1_, us2_) =
      begin
        matchExp (g_, us1_, us2_);
        awakeCnstr (Unify.nextCnstr ())
      end

    and awakeCnstr = function
      | None -> ()
      | Some { contents = Solved } -> awakeCnstr (Unify.nextCnstr ())
      | Some ({ contents = Eqn (g_, u1_, u2_) } as cnstr) -> begin
          Unify.solveConstraint cnstr;
          match1 (g_, (u1_, id), (u2_, id))
        end
      | Some { contents = FgnCnstr (csfc_csid, csfc_ops) } -> begin
          if FgnCnstrStd.Awake.apply (csfc_csid, csfc_ops) () then ()
          else raise (Match "Foreign constraint violated")
        end

    let rec matchW (g_, us1_, us2_) =
      begin
        Unify.resetAwakenCnstrs ();
        match1W (g_, us1_, us2_)
      end

    let rec match_ (g_, us1_, us2_) =
      begin
        Unify.resetAwakenCnstrs ();
        match1 (g_, us1_, us2_)
      end
  end

  (* weakenSub (G1, s, ss) = w'

       Invariant:
       If    G |- s : G1        s patsub 
       and   G2 |- ss : G       ss strsub 
       then  G1 |- w' : G1'     w' weaksub 

       and   G2 |- w' o s o ss : G1'  is fully defined
       and   G1' is maximal such
    *)
  (* no other cases, ss is strsub *)
  (* prune (G, (U, s), ss, rOccur) = U[s][ss]

       !!! looks wrong to me -kw
       G |- U : V    G' |- s : G  (G' |- U[s] : V[s])
       G'' |- ss : G'

       !!! i would say
       G |- s : G'   G' |- U : V  (G  |- U[s] : V[s])
       G'' |- ss : G

       Effect: prunes EVars in U[s] according to ss
               raises Match if U[s][ss] does not exist, or rOccur occurs in U[s]
    *)
  (* = id *)
  (* let
                     val wi = Whnf.invert w
                      val V' = EClo (V, wi) 
                     val V' = pruneExp (GX, (V, id), wi, rOccur)
                      val GY = Whnf.strengthen (wi, GX) 
                     val GY = pruneCtx (wi, GX, rOccur)
                      shortcut on GY possible by invariant on GX and V[s]? -fp 
                      could optimize by checking for identity subst 
                     val Y = newEVar (GY, V')
                     val Yw = EClo (Y, w)
                     val _ = Unify.instantiateEVar (r, Yw, !cnstrs)
                   in
                     EClo (Yw, comp (s, ss))
                   end*)
  (* s not patsub *)
  (* -bp not sure what to do in the non-pattern case *)
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
  (* below my raise Match *)
  (* pruneSub (G, Dot (Undef, s), ss, rOccur) is impossible *)
  (* By invariant, all EVars X[s] are such that s is defined everywhere *)
  (* Pruning establishes and maintains this invariant *)
  (* matchExpW (G, (U1, s1), (U2, s2)) = ()

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
            else exception Match is raised
       Other effects: EVars may be lowered
                      constraints may be added for non-patterns
    *)
  (* L1 = L2 = type, by invariant *)
  (* matchUni (L1, L2) - removed Mon Aug 24 12:18:24 1998 -fp *)
  (* s1 = s2 = id by whnf *)
  (* order of calls critical to establish matchSpine invariant *)
  (* because of strict *)
  (*  matchExpW (G, Whnf.expandDef (Us1), Whnf.expandDef (Us2)) *)
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
  (*      | matchExpW (G, Us1 as (U1 as EVar(r1, G1, V1, cnstrs1), s1),
                   Us2 as (U2 as EVar(r2, G2, V2, cnstrs2), s2)) =
           postpone, if s1 or s2 are not patsub 
          if r1 = r2 then
            if Whnf.isPatSub(s1) then
              if Whnf.isPatSub(s2) then
                let
                  val s' = Unify.intersection (s1,s2)    compute ss' directly? 
                in
                   without the next optimization, bugs/hangs/sources.cfg
                     would gets into an apparent infinite loop
                     Fri Sep  5 20:23:27 2003 -fp
                  
                  if Whnf.isId s'  added for definitions Mon Sep  1 19:53:13 2003 -fp 
                    then ()  X[s] = X[s] 
                  else let val ss' = Whnf.invert s'
                           val V1' = EClo (V1, ss')   invertExp ((V1, id), s', ref NONE) 
                           val G1' = Whnf.strengthen (ss', G1)
                       in
                         Unify.instantiateEVar (r1, EClo (newEVar (G1', V1'), s'), !cnstrs1)
                       end
                end
              else Unify.addConstraint (cnstrs2, ref (Eqn (G, EClo Us2, EClo Us1)))
            else Unify.addConstraint (cnstrs1, ref (Eqn (G, EClo Us1, EClo Us2)))
          else
            if Whnf.isPatSub(s1) then
              let
                val ss1 = Whnf.invert s1
                val U2' = pruneExp (G, Us2, ss1, r1)
              in
                 Unify.instantiateEVar (r1, EClo (U2, comp(s2, ss1)), !cnstrs1) 
                 invertExpW (Us2, s1, ref NONE) 
                Unify.instantiateEVar (r1, U2', !cnstrs1)
              end
            else if Whnf.isPatSub(s2) then
              let
                val ss2 = Whnf.invert s2
                val U1' = pruneExp (G, Us1, ss2, r2)
              in
                 instantiateEVar (r2, EClo (U1, comp(s1, ss2)), !cnstr2) 
                 invertExpW (Us1, s2, ref NONE) 
                Unify.instantiateEVar (r2, U1', !cnstrs2)
              end
            else
              let
                val cnstr = ref (Eqn (G, EClo Us1, EClo Us2))
              in
                Unify.addConstraint (cnstrs1, cnstr)
              end
*)
  (* instantiateEVar (r, EClo (U2, comp(s2, ss)), !cnstrs) *)
  (* invertExpW (Us2, s, r) *)
  (*      | matchExpW (G, Us1 as (U1,s1), Us2 as (EVar (r, GX, V, cnstrs), s)) =
        if Whnf.isPatSub(s) then
          let
            val ss = Whnf.invert s
            val U1' = pruneExp (G, Us1, ss, r)
          in
             instantiateEVar (r, EClo (U1, comp(s1, ss)), !cnstrs) 
             invertExpW (Us1, s, r) 
            instantiateEVar (r, U1', !cnstrs)
          end
        else
        Unify.addConstraint (cnstrs, ref (Eqn (G, EClo Us1, EClo Us2)))*)
  (* covers most remaining cases *)
  (* the cases for EClo or Redex should not occur because of whnf invariant *)
  (* matchExp (G, (U1, s1), (U2, s2)) = ()
       as in matchExpW, except that arguments may not be in whnf
    *)
  (*  matchExpW (G, Whnf.expandDef (Us1), Whnf.expandDef (Us2)) *)
  (* conservative *)
  (* matchSpine (G, (S1, s1), (S2, s2)) = ()

       Invariant:
       If   G |- s1 : G1   G1 |- S1 : V1 > W1
       and  G |- s2 : G2   G2 |- S2 : V2 > W2
       and  G |- V1 [s1] = V2 [s2]  : L    (for some level L)
       and  G |- W1 [s1] = W2 [s2]
       then if   there is an instantiation I :
                 s.t. G |- S1 [s1] <I> == S2 [s2] <I>
            then instantiation is applied as effect, () returned
            else exception Match is raised
       Other effects: EVars may be lowered,
                      constraints may be added for non-patterns
    *)
  (* Nil/App or App/Nil cannot occur by typing invariants *)
  (* matchSub (G, s1, s2) = ()

       Invariant:
       If   G |- s1 : G'
       and  G |- s2 : G'
       then matchSub (G, s1, s2) terminates with ()
            iff there exists an instantiation I, such that
            s1 [I] = s2 [I]

       Remark:  matchSub is used only to match the instantiation of SOME variables
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
  (* invariant? always k1 = k2? *)
  (* prune t2? Sat Dec  7 22:09:53 2002 *)
  (*
              if k1 < k2 then instantiateLVar (r1, LVar(r2, Shift(k2-k1), (l2, t2)))
                else Unify.instantiateLVar (r2, LVar(r1, Shift (k1-k2), (l1, t1)))
              *)
  (* hack! *)
  (* 0 = k2-k1 *)
  (* -- ABP *)
  (* -- ABP *)
  (*      | matchBlockW (G, LVar (r1, Shift(k1), (l1, t1)), Bidx i2) =
            (r1 := SOME (Bidx (i2 -k1)) ; ())  -- ABP 

      | matchBlockW (G, Bidx i1, LVar (r2, Shift(k2), (l2, t2))) =
            (r2 := SOME (Bidx (i1 -k2)) ; ())  -- ABP 
*)
  (* How can the next case arise? *)
  (* Sat Dec  8 11:49:16 2001 -fp !!! *)
  (*
      | matchBlock (LVar (r1, _, _), B as Bidx _) = instantiate (r1, B)
      | matchBlock (B as Bidx _, LVar (r2, _, _)) =

      This is still difficult --- B must make sense in the context of the LVar
      Shall we use the inverse of a pattern substitution? Or postpone as
      a constraint if pattern substitution does not exist?
      Sun Dec  1 11:33:13 2002 -cs

*)
  let matchW = matchW
  let match_ = match_
  let matchSub = matchSub
  let matchBlock = matchBlock

  let rec instance (g_, us1_, us2_) =
    try
      begin
        match_ (g_, us1_, us2_);
        true
      end
    with Match msg -> false

  let rec instance' (g_, us1_, us2_) =
    try
      begin
        match_ (g_, us1_, us2_);
        None
      end
    with Match msg -> Some msg
end
(* functor Match *)

(* # 1 "src/lambda/match.sml.ml" *)
