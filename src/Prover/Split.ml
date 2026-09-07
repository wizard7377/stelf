open! Intsyn.Lambda_
open! Global.Global_
open! Print.Print_
open! Index.Index_
open! Typecheck.Typecheck_
open! Solvers.Solvers_

(* # 1 "src/prover/Split.sig.ml" *)

(* Splitting: Version 1.4 *)
(* Author: Carsten Schuermann *)
include SPLIT
(* signature Split *)

(* # 1 "src/prover/Split.fun.ml" *)
open! Basis

exception Error of string

let () =
  Printexc.register_printer (function Error msg -> Some msg | _ -> None)

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
  module Subordinate : Subordinate.Subordinate_.SUBORDINATE
end) : SPLIT with module State = Split__0.State' = struct
  (*! structure IntSyn = IntSyn' !*)
  (*! structure Tomega = Tomega' !*)
  module State = Split__0.State'

  exception Error = Error

  type operator_ = Split of Tomega.prg option ref * Tomega.prg * string

  open! struct
    module T = Tomega
    module I = IntSyn
    module S = Split__0.State'
    module Subordinate = Split__0.Subordinate
    module Unify = Split__0.Unify

    let rec weaken a1 b1 = match a1, b1 with
      | I.Null, a -> I.id
      | I.Decl (g', (I.Dec (name, v) as d)), a ->
          let w' = weaken g' a in
          begin if Subordinate.belowEq (I.targetFam v) a then I.dot1 w'
          else I.comp w' I.shift
          end

    let createEVar (g, v) =
      let w = weaken g (I.targetFam v) in
      let iw = Whnf.invert w in
      let g' = Whnf.strengthen iw g in
      let x' = I.newEVar g' (I.EClo (v, iw)) in
      let x = I.EClo (x', w) in
      x

    let rec instEVars (vs, p, xsRev) = instEVarsW (Whnf.whnf vs, p, xsRev)

    and instEVarsW (vs, p, xsRev) = match vs, p with
      | vs, 0 -> (vs, xsRev)
      | (I.Pi ((I.Dec (xOpt, v1), _), v2), s), p ->
          let x1 = I.newEVar I.Null (I.EClo (v1, s)) in
          instEVars ((v2, I.Dot (I.Exp x1, s)), p - 1, Some x1 :: xsRev)
      | (I.Pi ((I.BDec (_, (l, t)), _), v2), s), p ->
          let l1 = I.newLVar (I.Shift 0) (l, I.comp t s) in
          instEVars ((v2, I.Dot (I.Block l1, s)), p - 1, None :: xsRev)

    open! struct
      let caseList : (T.dec I.ctx * T.sub) list ref = ref []
    end

    let resetCases () = caseList := []
    let addCase (psi, t) = caseList := (psi, t) :: !caseList
    let getCases () = !caseList

    let rec createEVarSpine (g, vs) = createEVarSpineW (g, Whnf.whnf vs)

    and createEVarSpineW (g, a) = match a with
      | ((I.Root _, s) as vs) -> (I.Nil, vs)
      | (I.Pi (((I.Dec (_, v1) as d), _), v2), s) ->
          let x = createEVar (g, I.EClo (v1, s)) in
          let s_, vs = createEVarSpine (g, (v2, I.Dot (I.Exp x, s))) in
          (I.App (x, s_), vs)

    let createAtomConst g h =
      let cid =
        match h with I.Const c -> c | I.Def c -> c | _ -> assert false
      in
      let v = I.constType cid in
      let s, vs = createEVarSpine (g, (v, I.id)) in
      (I.Root (h, s), vs)

    let createAtomBVar g k =
      let (I.Dec (_, v)) = I.ctxDec g k in
      let s, vs = createEVarSpine (g, (v, I.id)) in
      (I.Root (I.BVar k, s), vs)

    let createAtomProj (g, h, (v, s)) =
      let s_, vs' = createEVarSpine (g, (v, s)) in
      (I.Root (h, s_), vs')

    let rec constCases (g, vs, a, sc) = match a with
      | [] -> ()
      | (I.Const c as h) :: sgn' ->
          let u, vs' = createAtomConst g h in
          ignore (CsManager.trail (function () ->
                begin if Unify.unifiable g vs vs' then sc u else ()
                end));
          constCases (g, vs, sgn', sc)
      | (I.Def c as h) :: sgn' ->
          let u, vs' = createAtomConst g h in
          ignore (CsManager.trail (function () ->
                begin if Unify.unifiable g vs vs' then sc u else ()
                end));
          constCases (g, vs, sgn', sc)
      | _ :: sgn' ->
          (* Skip other head types *)
          constCases (g, vs, sgn', sc)

    let rec paramCases (g, vs, k, sc) = match k with
      | 0 -> ()
      | k ->
          let u, vs' = createAtomBVar g k in
          ignore (CsManager.trail (function () ->
                begin if Unify.unifiable g vs vs' then sc u else ()
                end));
          paramCases (g, vs, k - 1, sc)

    let rec createEVarSub = function
      | I.Null -> I.id
      | I.Decl (g', (I.Dec (_, v) as d)) ->
          let s = createEVarSub g' in
          let v' = I.EClo (v, s) in
          let x = I.newEVar I.Null v' in
          I.Dot (I.Exp x, s)

    let blockName cid = I.conDecName (I.sgnLookup cid)

    let rec blockCases (g, vs, cid, (gsome, piDecs), sc) =
      let t = createEVarSub gsome in
      let sk = I.Shift (I.ctxLength g) in
      let t' = I.comp t sk in
      let lvar = I.newLVar sk (cid, t') in
      blockCases' (g, vs, (lvar, 1), (t', piDecs), sc)

    and blockCases' (g, vs, a, b, sc) = match a, b with
      | (lvar, i), (t, []) -> ()
      | (lvar, i), (t, I.Dec (_, v') :: piDecs) ->
          let u, vs' = createAtomProj (g, I.Proj (lvar, i), (v', t)) in
          ignore (CsManager.trail (function () ->
                begin if Unify.unifiable g vs vs' then sc u else ()
                end));
          let t' = I.Dot (I.Exp (I.Root (I.Proj (lvar, i), I.Nil)), t) in
          blockCases' (g, vs, (lvar, i + 1), (t', piDecs), sc)

    let rec worldCases (g, vs, a, sc) = match a with
      | T.Worlds [] -> ()
      | T.Worlds (cid :: cids) -> begin
          blockCases (g, vs, cid, I.constBlock cid, sc);
          worldCases (g, vs, T.Worlds cids, sc)
        end

    let rec lowerSplit (g, vs, w, sc) =
      lowerSplitW (g, Whnf.whnf vs, w, sc)

    and lowerSplitW (g, ((I.Root (I.Const a, _), s) as vs), w, sc) =
      ignore (constCases (g, vs, Index.lookup a, sc));
      ignore (paramCases (g, vs, I.ctxLength g, sc));
      ignore (worldCases (g, vs, w, sc));
      ()

    let splitEVar ((I.EVar (_, gx, v, _) as x), w, sc) =
      lowerSplit
        ( I.Null,
          (v, I.id),
          w,
          function
          | u ->
              begin if Unify.unifiable I.Null (x, I.id) (u, I.id) then
                sc ()
              else ()
              end )

    let rec createSub = function
      | I.Null -> T.id
      | I.Decl (psi, T.UDec (I.Dec (xOpt, v1))) ->
          let t' = createSub psi in
          let v1', s' = Whnf.whnf (v1, T.coerceSub t') in
          let x = I.newEVar I.Null (I.EClo (v1', s')) in
          T.Dot (T.Exp x, t')
      | I.Decl (psi, T.UDec (I.BDec (_, (l, s)))) ->
          let t' = createSub psi in
          let l_ = I.newLVar (I.Shift 0) (l, I.comp s (T.coerceSub t')) in
          T.Dot (T.Block l_, t')
      | I.Decl (psi, T.PDec (_, f, tc1, tc2)) ->
          let t' = createSub psi in
          let y = T.newEVarTC (I.Null, T.FClo (f, t'), tc1, tc2) in
          T.Dot (T.Prg y, t')

    let rec mkCases (a, f) = match a with
      | [] -> []
      | (psi, t) :: cs ->
          let x = T.newEVar psi (T.FClo (f, t)) in
          (psi, t, x) :: mkCases (cs, f)

    let split (S.Focus (T.EVar (psi, r, f, None, None, _), w)) =
      let rec splitXs arg__1 arg__2 =
        begin match (arg__1, arg__2) with
        | (g, i), ([], _, _, _) -> []
        | (g, i), (x :: xs, f, w, sc) ->
            ignore (Display.chatter_s 6
                (("Split " ^ Print.expToString I.Null x) ^ ".\n"));
            let os = splitXs (g, i + 1) (xs, f, w, sc) in
            ignore (resetCases ());
            let s = Print.expToString g x in
            let os' =
              try
                begin
                  splitEVar (x, w, sc);
                  Split (r, T.Case (T.Cases (mkCases (getCases (), f))), s)
                  :: os
                end
              with Constraints.Error constrs ->
                begin
                  Display.chatter_s 6
                    (("Inactive split:\n" ^ Print.cnstrsToString constrs) ^ "\n");
                  os
                end
            in
            os'
        end
      in
      let t = createSub psi in
      let xs = State.collectLFSub t in
      let init () = addCase (Abstract.abstractTomegaSub t) in
      let g = T.coerceCtx psi in
      let os = splitXs (g, 1) (xs, f, w, init) in
      os

    let expand (S.Focus (T.EVar (psi, r, f, None, None, _), w) as s) =
      begin if Abstract.closedCTX psi then split s else []
      end

    let apply (Split (r, p, s)) = r := Some p
    let menu (Split (_, _, s)) = "Split " ^ s
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
       to be Split.  Maintained as a mutable reference so it
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

(* # 1 "src/prover/Split.sml.ml" *)
