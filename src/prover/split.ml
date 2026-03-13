(* # 1 "src/prover/split.sig.ml" *)
open! Basis

(* Splitting: Version 1.4 *)
(* Author: Carsten Schuermann *)
module type SPLIT = sig
  (*! structure IntSyn : INTSYN !*)
  (*! structure Tomega : TOMEGA !*)
  module State : State.STATE

  exception Error of string

  type nonrec operator

  val expand : State.focus_ -> operator list
  val apply : operator -> unit
  val menu : operator -> string
end
(* signature Split *)

(* # 1 "src/prover/split.fun.ml" *)
open! Basis

module Split (Split__0 : sig
  (* State definition for Proof Search *)
  (* Author: Carsten Schuermann *)
  module Global : GLOBAL

  (*! structure IntSyn' : INTSYN !*)
  (*! structure Tomega' : TOMEGA !*)
  (*! sharing Tomega'.IntSyn = IntSyn' !*)
  module State' : State.STATE

  (*! sharing State'.IntSyn = IntSyn' !*)
  (*! sharing State'.Tomega = Tomega' !*)
  module Whnf : WHNF

  (*! sharing Whnf.IntSyn = IntSyn' !*)
  module Unify : UNIFY

  (*! sharing Unify.IntSyn = IntSyn' !*)
  module Constraints : CONSTRAINTS

  (*! sharing Constraints.IntSyn = IntSyn' !*)
  module Abstract : ABSTRACT

  (*! sharing Abstract.IntSyn = IntSyn' !*)
  (*! sharing Abstract.Tomega = Tomega' !*)
  module Index : INDEX

  (*! sharing Index.IntSyn = IntSyn' !*)
  module Print : PRINT

  (*! sharing Print.IntSyn = IntSyn' !*)
  module TypeCheck : TYPECHECK

  (*! sharing TypeCheck.IntSyn = IntSyn' !*)
  module Subordinate : SUBORDINATE
end) : SPLIT with module State = Split__0.State' = struct
  (*! structure IntSyn = IntSyn' !*)
  (*! structure Tomega = Tomega' !*)
  module State = Split__0.State'

  exception Error of string

  type operator_ = Split of Tomega.prg_ option ref * Tomega.prg_ * string

  open! struct
    module T = Tomega
    module I = IntSyn
    module S = Split__0.State'
    module Unify = Split__0.Unify

    let rec weaken = function
      | null_, a -> I.id
      | I.Decl (g'_, (I.Dec (name, v_) as d_)), a ->
          let w' = weaken (g'_, a) in
          begin if Subordinate.belowEq (I.targetFam v_, a) then I.dot1 w'
          else I.comp (w', I.shift)
          end

    let rec createEVar (g_, v_) =
      let w = weaken (g_, I.targetFam v_) in
      let iw = Whnf.invert w in
      let g'_ = Whnf.strengthen (iw, g_) in
      let x'_ = I.newEVar (g'_, I.EClo (v_, iw)) in
      let x_ = I.EClo (x'_, w) in
      x_

    let rec instEVars (vs_, p, xsRev_) = instEVarsW (Whnf.whnf vs_, p, xsRev_)

    and instEVarsW = function
      | vs_, 0, xsRev_ -> (vs_, xsRev_)
      | (I.Pi ((I.Dec (xOpt, v1_), _), v2_), s), p, xsRev_ ->
          let x1_ = I.newEVar (I.null_, I.EClo (v1_, s)) in
          instEVars ((v2_, I.Dot (I.Exp x1_, s)), p - 1, Some x1_ :: xsRev_)
      | (I.Pi ((I.BDec (_, (l, t)), _), v2_), s), p, xsRev_ ->
          let l1_ = I.newLVar (I.Shift 0, (l, I.comp (t, s))) in
          instEVars ((v2_, I.Dot (I.Block l1_, s)), p - 1, None :: xsRev_)

    open! struct
      let caseList : (T.dec_ I.ctx_ * T.sub_) list ref = ref []
    end

    let rec resetCases () = caseList := []
    let rec addCase (psi_, t) = caseList := (psi_, t) :: !caseList
    let rec getCases () = !caseList

    let rec createEVarSpine (g_, vs_) = createEVarSpineW (g_, Whnf.whnf vs_)

    and createEVarSpineW = function
      | g_, ((I.Root _, s) as vs_) -> (I.Nil, vs_)
      | g_, (I.Pi (((I.Dec (_, v1_) as d_), _), v2_), s) ->
          let x_ = createEVar (g_, I.EClo (v1_, s)) in
          let s_, vs_ = createEVarSpine (g_, (v2_, I.Dot (I.Exp x_, s))) in
          (I.App (x_, s_), vs_)

    let rec createAtomConst (g_, (I.Const cid as h_)) =
      let v_ = I.constType cid in
      let s_, vs_ = createEVarSpine (g_, (v_, I.id)) in
      (I.Root (h_, s_), vs_)

    let rec createAtomBVar (g_, k) =
      let (I.Dec (_, v_)) = I.ctxDec (g_, k) in
      let s_, vs_ = createEVarSpine (g_, (v_, I.id)) in
      (I.Root (I.BVar k, s_), vs_)

    let rec createAtomProj (g_, h_, (v_, s)) =
      let s_, vs'_ = createEVarSpine (g_, (v_, s)) in
      (I.Root (h_, s_), vs'_)

    let rec constCases = function
      | g_, vs_, [], sc -> ()
      | g_, vs_, I.Const c :: sgn', sc ->
          let u_, vs'_ = createAtomConst (g_, I.Const c) in
          let _ =
            Cs_manager.trail (function () ->
                begin if Unify.unifiable (g_, vs_, vs'_) then sc u_ else ()
                end)
          in
          constCases (g_, vs_, sgn', sc)

    let rec paramCases = function
      | g_, vs_, 0, sc -> ()
      | g_, vs_, k, sc ->
          let u_, vs'_ = createAtomBVar (g_, k) in
          let _ =
            Cs_manager.trail (function () ->
                begin if Unify.unifiable (g_, vs_, vs'_) then sc u_ else ()
                end)
          in
          paramCases (g_, vs_, k - 1, sc)

    let rec createEVarSub = function
      | null_ -> I.id
      | I.Decl (g'_, (I.Dec (_, v_) as d_)) ->
          let s = createEVarSub g'_ in
          let v'_ = I.EClo (v_, s) in
          let x_ = I.newEVar (I.null_, v'_) in
          I.Dot (I.Exp x_, s)

    let rec blockName cid = I.conDecName (I.sgnLookup cid)

    let rec blockCases (g_, vs_, cid, (gsome_, piDecs), sc) =
      let t = createEVarSub gsome_ in
      let sk = I.Shift (I.ctxLength g_) in
      let t' = I.comp (t, sk) in
      let lvar = I.newLVar (sk, (cid, t')) in
      blockCases' (g_, vs_, (lvar, 1), (t', piDecs), sc)

    and blockCases' = function
      | g_, vs_, (lvar, i), (t, []), sc -> ()
      | g_, vs_, (lvar, i), (t, I.Dec (_, v'_) :: piDecs), sc ->
          let u_, vs'_ = createAtomProj (g_, I.Proj (lvar, i), (v'_, t)) in
          let _ =
            Cs_manager.trail (function () ->
                begin if Unify.unifiable (g_, vs_, vs'_) then sc u_ else ()
                end)
          in
          let t' = I.Dot (I.Exp (I.Root (I.Proj (lvar, i), I.Nil)), t) in
          blockCases' (g_, vs_, (lvar, i + 1), (t', piDecs), sc)

    let rec worldCases = function
      | g_, vs_, T.Worlds [], sc -> ()
      | g_, vs_, T.Worlds (cid :: cids), sc -> begin
          blockCases (g_, vs_, cid, I.constBlock cid, sc);
          worldCases (g_, vs_, T.Worlds cids, sc)
        end

    let rec lowerSplit (g_, vs_, w_, sc) =
      lowerSplitW (g_, Whnf.whnf vs_, w_, sc)

    and lowerSplitW (g_, ((I.Root (I.Const a, _), s) as vs_), w_, sc) =
      let _ = constCases (g_, vs_, Index.lookup a, sc) in
      let _ = paramCases (g_, vs_, I.ctxLength g_, sc) in
      let _ = worldCases (g_, vs_, w_, sc) in
      ()

    let rec splitEVar ((I.EVar (_, gx_, v_, _) as x_), w_, sc) =
      lowerSplit
        ( I.null_,
          (v_, I.id),
          w_,
          function
          | u_ -> begin
              if Unify.unifiable (I.null_, (x_, I.id), (u_, I.id)) then sc ()
              else ()
            end )

    let rec createSub = function
      | null_ -> T.id
      | I.Decl (psi_, T.UDec (I.Dec (xOpt, v1_))) ->
          let t' = createSub psi_ in
          let v1'_, s'_ = Whnf.whnf (v1_, T.coerceSub t') in
          let x_ = I.newEVar (I.null_, I.EClo (v1'_, s'_)) in
          T.Dot (T.Exp x_, t')
      | I.Decl (psi_, T.UDec (I.BDec (_, (l, s)))) ->
          let t' = createSub psi_ in
          let l_ = I.newLVar (I.Shift 0, (l, I.comp (s, T.coerceSub t'))) in
          T.Dot (T.Block l_, t')
      | I.Decl (psi_, T.PDec (_, f_, tc1_, tc2_)) ->
          let t' = createSub psi_ in
          let y_ = T.newEVarTC (I.null_, T.FClo (f_, t'), tc1_, tc2_) in
          T.Dot (T.Prg y_, t')

    let rec mkCases = function
      | [], f_ -> []
      | (psi_, t) :: cs, f_ ->
          let x_ = T.newEVar (psi_, T.FClo (f_, t)) in
          (psi_, t, x_) :: mkCases (cs, f_)

    let rec split (S.Focus (T.EVar (psi_, r, f_, None, None, _), w_)) =
      let rec splitXs arg__1 arg__2 =
        begin match (arg__1, arg__2) with
        | (g_, i), ([], _, _, _) -> []
        | (g_, i), (x_ :: xs_, f_, w_, sc) ->
            let _ =
              begin if !Global.chatter >= 6 then
                print (("Split " ^ Print.expToString (I.null_, x_)) ^ ".\n")
              else ()
              end
            in
            let os_ = splitXs (g_, i + 1) (xs_, f_, w_, sc) in
            let _ = resetCases () in
            let s = Print.expToString (g_, x_) in
            let os'_ =
              try
                begin
                  splitEVar (x_, w_, sc);
                  Split (r, T.Case (T.Cases (mkCases (getCases (), f_))), s)
                  :: os_
                end
              with Constraints.Error constrs ->
                begin
                  begin if !Global.chatter >= 6 then
                    print
                      (("Inactive split:\n" ^ Print.cnstrsToString constrs)
                      ^ "\n")
                  else ()
                  end;
                  os_
                end
            in
            os'_
        end
      in
      let t = createSub psi_ in
      let xs_ = State.collectLFSub t in
      let rec init () = addCase (Abstract.abstractTomegaSub t) in
      let g_ = T.coerceCtx psi_ in
      let os_ = splitXs (g_, 1) (xs_, f_, w_, init) in
      os_

    let rec expand (S.Focus (T.EVar (psi_, r, f_, None, None, _), w_) as s_) =
      begin if Abstract.closedCTX psi_ then split s_ else []
      end

    let rec apply (Split (r, p_, s)) = r := Some p_
    let rec menu (Split (_, _, s)) = "Split " ^ s
  end

  (* weaken (G, a) = w'

       Invariant:
       If   a is a type family
       then G |- w' : G'
       and  forall x:A in G'  A subordinate to a
     *)
  (* added next case, probably should not arise *)
  (* Sun Dec 16 10:42:05 2001 -fp !!! *)
  (*
      | weaken (I.Decl (G', D as I.BDec _), a) =
           I.dot1 (weaken (G', a))
      *)
  (* createEVar (G, V) = X[w] where G |- X[w] : V

       Invariant:
       If G |- V : L
       then G |- X[w] : V
    *)
  (* G |- V : L *)
  (* G  |- w  : G'    *)
  (* G' |- iw : G     *)
  (* G' |- X' : V[iw] *)
  (* G  |- X  : V     *)
  (* instEVars ({x1:V1}...{xp:Vp} V, p, nil) = (V[s], [X1,...,Xn])
       where . |- s : {x1:V1}...{xp:Vp}
       and s = Xp...X1.id, all Xi are new EVars
    *)
  (* p > 0 *)
  (* all EVars are global *)
  (* G0 |- t : Gsome *)
  (* . |- s : G0 *)
  (* p > 0 *)
  (* --cs Sun Dec  1 06:33:27 2002 *)
  (* caseList is a list of possibilities for a variables
       to be split.  Maintained as a mutable reference so it
       can be updated in the success continuation.
    *)
  (* createEVarSpine (G, (V, s)) = (S', (V', s'))

       Invariant:
       If   G |- s : G1   and  G1 |- V = Pi {V1 .. Vn}. W : L
       and  G1, V1 .. Vn |- W atomic
       then G |- s' : G2  and  G2 |- V' : L
       and  S = X1; ...; Xn; Nil
       and  G |- W [1.2...n. s o ^n] = V' [s']
       and  G |- S : V [s] >  V' [s']
    *)
  (* s = id *)
  (* G |- V1[s] : L *)
  (* Uni or other cases should be impossible *)
  (* createAtomConst (G, c) = (U', (V', s'))

       Invariant:
       If   S |- c : Pi {V1 .. Vn}. V
       then . |- U' = c @ (X1; .. Xn; Nil)
       and  . |- U' : V' [s']
    *)
  (* createAtomBVar (G, k) = (U', (V', s'))

       Invariant:
       If   G |- k : Pi {V1 .. Vn}. V
       then . |- U' = k @ (Xn; .. Xn; Nil)
       and  . |- U' : V' [s']
    *)
  (* createAtomProj (G, #i(l), (V, s)) = (U', (V', s'))

       Invariant:
       If   G |- #i(l) : Pi {V1 .. Vn}. Va
       and  G |- Pi {V1..Vn}. Va = V[s] : type
       then . |- U' = #i(l) @ (X1; .. Xn; Nil)
       and  . |- U' : V' [s']
    *)
  (* createEVarSub G' = s

       Invariant:
       If   . |- G' ctx
       then . |- s : G' and s instantiates each x:A with an EVar . |- X : A

       Update: Always use empty context. Sat Dec  8 13:19:58 2001 -fp
    *)
  (* hack *)
  (* blockCases (G, Vs, B, (Gsome, piDecs), sc) =

       If G |- V[s] : type
          . |- Gsome ctx and Gsome |- piDecs decList
       then sc is called for any x:A in piDecs such thtat
            G |- V[s] = A[t] : type
            where t instantiates variable in Gsome with new EVars
    *)
  (* accounts for subordination *)
  (* . |- t : Gsome *)
  (* --cs Sun Dec  1 06:33:41 2002 *)
  (* G |- t' : Gsome *)
  (* G |- t : G' and G' |- ({_:V'},piDecs) decList *)
  (* so G |- V'[t'] : type *)
  (* will trail *)
  (* will trail *)
  (* will trail *)
  (*     | lowerSplitW (G, (I.Pi ((D, P), V), s), W, sc) =
        let
          val D' = I.decSub (D, s)
        in
          lowerSplit (I.Decl (G, D'), (V, I.dot1 s), W, fn U => sc (I.Lam (D', U)))
        end
      we assume that all EVars are lowere :-)
*)
  (* splitEVar (X, W, sc) = ()

       calls sc () for all cases, after instantiation of X
       W are the currently possible worlds
    *)
  (* GX = I.Null *)
  (* createSub (Psi) = s

       Invariant:
       If   Psi is a meta context
       then s = Xp...X1.id, all Xi are new EVars/LVars/MVars
       and  . |- s : Psi
    *)
  (* all EVars are global and lowered *)
  (* Psi0 |- t : Gsome *)
  (* . |- s : Psi0 *)
  (* --cs Sun Dec  1 06:34:00 2002 *)
  (* p > 0 *)
  (* mkCases L F= Ss

       Invariant:
       If   L is a list of cases (Psi1, t1) .... (Psin, tn)
       and  Psii |- ti : Psi
       and  Psi  |- F formula
       then Ss is a list of States S1 ... Sn
       and  Si = (Psii, Fi)
       where  Psii |- Fi = F [ti]  formula
    *)
  (* split S = S1 ... Sn

       Invariant:
       If   S = (P |> F)
       then Si = (Pi |> Fi)
       s.t. there exists substitution si
            and  Pi |- si : P
            and  Pi |- Fi = F[si]
            and  for every G |- t : P,

                 there ex. an i among 1..n
                 and a substitution t',
                 s.t. G |- t' : Pi
                 and  t = t' [si]
    *)
  (* splitXs (G, i) (Xs, F, W, sc) = Os
           Invariant:
           If   Psi is a CONTEXT
           and  G ~ Psi a context,
           and  G |- i : V
           and  Psi |- F formula
           and  Xs are all logic variables
           then Os is a list of splitting operators
        *)
  (* returns a list of operators *)
  (*            val I.Dec (SOME s, _) = I.ctxLookup (G, i) *)
  (* . |- t :: Psi *)
  (* apply (Op) = Sl'

       Invariant:
       If   Op = (_, Sl)
       then Sl' = Sl

       Side effect: If Sl contains inactive states, an exception is raised
    *)
  (* trailing required -cs Thu Apr 22 12:05:04 2004 *)
  type nonrec operator = operator_

  let expand = expand
  let apply = apply
  let menu = menu
end
(*! sharing Subordinate.IntSyn = IntSyn' !*)
(* functor Split *)

(* # 1 "src/prover/split.sml.ml" *)
