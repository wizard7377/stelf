(* # 1 "src/tomega/Opsem.sig.ml" *)
open! Basis
module Tomega = Lambda_.Tomega

(* Operational Semantics for Delphin *)
(* Author: Carsten Schuermann *)
include OPSEM

(* # 1 "src/tomega/Opsem.fun.ml" *)
open! Basis

exception Error of string

let () =
  Printexc.register_printer (function Error msg -> Some msg | _ -> None)

exception Abort

let () =
  Printexc.register_printer (function Abort -> Some "Abort" | _ -> None)

exception NoMatch

let () =
  Printexc.register_printer (function NoMatch -> Some "NoMatch" | _ -> None)

module MakeOpsem
    (Whnf : WHNF)
    (Abstract : ABSTRACT)
    (Subordinate : Subordinate.Subordinate_.SUBORDINATE)
    (TomegaTypeCheck : TOMEGATYPECHECK.TOMEGATYPECHECK)
    (TomegaPrint : Tomegaprint.TOMEGAPRINT)
    (Unify : UNIFY) : OPSEM = struct
  (*
  (* Internal syntax for functional proof term calculus *)
  (* Author: Carsten Schuermann, Adam Poswolsky *)
  module Whnf : WHNF
  module Abstract : ABSTRACT
  module Subordinate : Subordinate.Subordinate_.SUBORDINATE
  module TomegaTypeCheck : TOMEGATYPECHECK.TOMEGATYPECHECK
  module TomegaPrint : Tomegaprint.TOMEGAPRINT
  module Unify : UNIFY
*)
  module T = Tomega
  module I = IntSyn
  module S = Subordinate
  module A = Abstract
  module Unify = Unify
  module TomegaPrint = TomegaPrint

  exception Error = Error
  exception Abort = Abort

  (*  local -- removed ABP 1/19/03 *)
  exception NoMatch = NoMatch

  (*
 matchPrg is used to see if two values can be 'unified' for
   purpose of matching case

 matchPrg (Psi, P1, P2) = ()

    Invariant:
    If P1 has no EVARs and P2 possibly does.
    and Psi  |- P1 :: F
    and Psi |- P1 value
    and Psi |- P2 :: F
    and Psi |- P2 value
     then if Psi |- P1 == P2 matchPrg terminates
       otherwise exception NoMatch is raised
*)
  let rec matchPrg (psi, p1_, p2_) =
    matchVal (psi, (p1_, T.id), T.normalizePrg (p2_, T.id))

  and matchVal = function
    | psi, (T.Unit, _), T.Unit -> ()
    | psi, (T.PairPrg (p1_, p1'), t1), T.PairPrg (p2_, p2') -> begin
        matchVal (psi, (p1_, t1), p2_);
        matchVal (psi, (p1', t1), p2')
      end
    | psi, (T.PairBlock (b1_, p1_), t1), T.PairBlock (b2_, p2_) -> begin
        matchVal (psi, (p1_, t1), p2_);
        try
          Unify.unifyBlock
            (T.coerceCtx psi, I.blockSub (b1_, T.coerceSub t1), b2_)
        with Unify.Unify _ -> raise NoMatch
      end
    | psi, (T.PairExp (u1_, p1_), t1), T.PairExp (u2_, p2_) -> begin
        matchVal (psi, (p1_, t1), p2_);
        try Unify.unify (T.coerceCtx psi, (u1_, T.coerceSub t1), (u2_, I.id))
        with Unify.Unify _ -> raise NoMatch
      end
    | psi, (T.PClo (p_, t1'), t1), pt ->
        matchVal (psi, (p_, T.comp (t1', t1)), pt)
    | psi, (p'_, t1), T.PClo (T.PClo (p_, t2), t3) ->
        matchVal (psi, (p'_, t1), T.PClo (p_, T.comp (t2, t3)))
    | ( psi,
        (p'_, t1),
        T.PClo (T.EVar (_, ({ contents = None } as r), _, _, _, _), t2) ) ->
        let iw = T.invertSub t2 in
        r := Some (T.PClo (p'_, T.comp (t1, iw)))
        (* ABP -- just make sure this is right *)
    | psi, (p'_, t1), T.EVar (_, ({ contents = None } as r), _, _, _, _) ->
        r := Some (T.PClo (p'_, t1))
    | psi, (v_, t), T.EVar (d_, ({ contents = Some p_ } as r), f_, _, _, _) ->
        matchVal (psi, (v_, t), p_)
    | _ -> raise NoMatch

  (* ABP -- this should never occur, since we normalized it to start *)
  (* ABP -- Do we need this? I added it *)
  (* Added by ABP *)

  (* ABP -- normalizePrg invariant does not state what happens to non-free EVArs,
       and there are some embedded under PClo... *)
  let rec append = function
    | g1_, I.Null -> g1_
    | g1_, I.Decl (g2_, d_) -> I.Decl (append (g1_, g2_), d_)

  and raisePrg = function
    | psi, g_, T.Unit -> T.Unit
    | psi, g_, T.PairPrg (p1_, p2_) ->
        let p1' = raisePrg (psi, g_, p1_) in
        let p2' = raisePrg (psi, g_, p2_) in
        T.PairPrg (p1', p2')
    | psi, g_, T.PairExp (u_, p_) ->
        let v_ = TypeCheck.infer' (append (T.coerceCtx psi, g_), u_) in
        let w = S.weaken (g_, I.targetFam v_) in
        let iw = Whnf.invert w in
        let g'_ = Whnf.strengthen (iw, g_) in
        let u'_ = A.raiseTerm (g'_, I.EClo (u_, iw)) in
        let p'_ = raisePrg (psi, g_, p_) in
        T.PairExp (u'_, p'_)
  (* this is a real time sink, it would be much better if we did not have to
      compute the type information of U,
      more thought is required
   *)

  (* G  |- w  : G'    *)
  (* G' |- iw : G     *)
  (* Psi0, G' |- B'' ctx *)
  and evalPrg = function
    | psi, (T.Unit, t) -> T.Unit
    | psi, (T.PairExp (m_, p_), t) ->
        T.PairExp (I.EClo (m_, T.coerceSub t), evalPrg (psi, (p_, t)))
    | psi, (T.PairBlock (b_, p_), t) ->
        T.PairBlock (I.blockSub (b_, T.coerceSub t), evalPrg (psi, (p_, t)))
    | psi, (T.PairPrg (p1_, p2_), t) ->
        T.PairPrg (evalPrg (psi, (p1_, t)), evalPrg (psi, (p2_, t)))
    | psi, (T.Redex (p_, s_), t) ->
        evalRedex (psi, evalPrg (psi, (p_, t)), (s_, t))
    | psi, (T.Var k, t) ->
        begin match T.varSub (k, t) with T.Prg p_ -> evalPrg (psi, (p_, T.id))
        end
    | psi, (T.Const lemma, t) -> evalPrg (psi, (T.lemmaDef lemma, t))
    | psi, (T.Lam ((T.UDec (I.BDec _) as d_), p_), t) ->
        let d'_ = T.decSub (d_, t) in
        T.Lam (d'_, evalPrg (I.Decl (psi, d'_), (p_, T.dot1 t)))
    | psi, (T.Lam (d_, p_), t) -> T.Lam (T.decSub (d_, t), T.PClo (p_, T.dot1 t))
    | psi, ((T.Rec (d_, p_) as p'_), t) ->
        evalPrg (psi, (p_, T.Dot (T.Prg (T.PClo (p'_, t)), t)))
    | psi, (T.PClo (p_, t'), t) -> evalPrg (psi, (p_, T.comp (t', t)))
    | psi, (T.Case (T.Cases o_), t') -> match_ (psi, t', T.Cases (rev o_))
    | psi, (T.EVar (d_, ({ contents = Some p_ } as r), f_, _, _, _), t) ->
        evalPrg (psi, (p_, t))
    | psi, (T.Let (d_, p1_, p2_), t) ->
        let v_ = evalPrg (psi, (p1_, t)) in
        let v'_ = evalPrg (psi, (p2_, T.Dot (T.Prg v_, t))) in
        v'_
    | psi, (T.New (T.Lam (d_, p_)), t) ->
        let d'_ = T.decSub (d_, t) in
        let (T.UDec d''_) = d'_ in
        let d''' = T.UDec (Names.decName (T.coerceCtx psi, d''_)) in
        let v_ = evalPrg (I.Decl (psi, d'''), (p_, T.dot1 t)) in
        let b_ = T.coerceCtx (I.Decl (I.Null, d''')) in
        let g_, t' = T.deblockify b_ in
        let newP = raisePrg (psi, g_, T.normalizePrg (v_, t')) in
        newP
        (* unnecessary naming, remove later --cs *)
    | psi, (T.Box (w_, p_), t) -> evalPrg (psi, (p_, t))
    | psi, (T.Choose p_, t) ->
        let rec substToSpine' = function
          | I.Shift n, I.Null, t_acc -> t_acc
          | I.Shift n, (I.Decl _ as g_), t_acc ->
              substToSpine' (I.Dot (I.Idx (n + 1), I.Shift (n + 1)), g_, t_acc)
          | I.Dot (I.Exp u_, s), I.Decl (g_, v_), t_acc ->
              substToSpine' (s, g_, T.AppExp (u_, t_acc))
          | I.Dot (I.Idx n, s), I.Decl (g_, I.Dec (_, v_)), t_acc ->
              let us_, _ =
                Whnf.whnfEta ((I.Root (I.BVar n, I.Nil), I.id), (v_, I.id))
              in
              substToSpine'
                ( s,
                  g_,
                  let u_eta, s_eta = us_ in
                  T.AppExp (I.EClo (u_eta, s_eta), t_acc) )
          (* Eta-expand *)
        in
        let rec choose = function
          | k, I.Null -> raise Abort
          | k, I.Decl (psi', T.PDec _) -> choose (k + 1, psi')
          | k, I.Decl (psi', T.UDec (I.Dec _)) -> choose (k + 1, psi')
          | k, I.Decl (psi', T.UDec (I.BDec (_, (l1, s1)))) -> (
              let gsome_, gpi = I.constBlock l1 in
              let s_ =
                substToSpine' (s1, gsome_, T.AppBlock (I.Bidx k, T.Nil))
              in
              try evalPrg (psi, (T.Redex (T.PClo (p_, t), s_), T.id))
              with Abort -> choose (k + 1, psi'))
        in
        choose (1, psi)
  (* This function was imported from Cover.fun. *)

  and match_ = function
    | psi, t1, T.Cases ((psi', t2, p_) :: c_) -> (
        let t = createVarSub (psi, psi') in
        let t' = T.comp (t2, t) in
        try
          begin
            matchSub (psi, t1, t');
            evalPrg (psi, (p_, t) (*T.normalizeSub*))
          end
        with NoMatch -> match_ (psi, t1, T.Cases c_)
        (* val I.Null = Psi *)
        (* Psi |- t : Psi' *)
        (* Psi' |- t2 . shift(k) : Psi'' *)
        (* Note that since we are missing the shift(k), it is possible
           * that t' has extra DOTs in there that weren't removed *)
        )
    | psi, t1, T.Cases [] -> raise Abort

  and createVarSub = function
    | psi, I.Null -> T.Shift (I.ctxLength psi)
    | psi, (I.Decl (psi', T.PDec (name, f_, None, None)) as psi'') ->
        let t = createVarSub (psi, psi') in
        let t' =
          T.Dot (T.Prg (T.newEVarTC (psi, T.forSub (f_, t), None, None)), t)
        in
        t'
    | psi, I.Decl (psi', T.UDec (I.Dec (name, v_))) ->
        let t = createVarSub (psi, psi') in
        T.Dot
          ( T.Exp
              (I.EVar
                 (ref None, T.coerceCtx psi, I.EClo (v_, T.coerceSub t), ref [])),
            t )
    | psi, I.Decl (psi', T.UDec (I.BDec (name, (cid, s)))) ->
        let t = createVarSub (psi, psi') in
        T.Dot
          ( T.Block (I.LVar (ref None, I.id, (cid, I.comp (s, T.coerceSub t)))),
            t )

  and matchSub = function
    | psi, _, T.Shift _ -> ()
    | psi, T.Shift n, (T.Dot _ as t) ->
        matchSub (psi, T.Dot (T.Idx (n + 1), T.Shift (n + 1)), t)
    | psi, T.Dot (T.Exp u1_, t1), T.Dot (T.Exp u2_, t2) -> begin
        matchSub (psi, t1, t2);
        try Unify.unify (T.coerceCtx psi, (u1_, I.id), (u2_, I.id))
        with Unify.Unify s -> raise NoMatch
      end
    | psi, T.Dot (T.Exp u1_, t1), T.Dot (T.Idx k, t2) -> begin
        matchSub (psi, t1, t2);
        try
          Unify.unify
            (T.coerceCtx psi, (u1_, I.id), (I.Root (I.BVar k, I.Nil), I.id))
        with Unify.Unify _ -> raise NoMatch
      end
    | psi, T.Dot (T.Idx k, t1), T.Dot (T.Exp u2_, t2) -> begin
        matchSub (psi, t1, t2);
        try
          Unify.unify
            (T.coerceCtx psi, (I.Root (I.BVar k, I.Nil), I.id), (u2_, I.id))
        with Unify.Unify _ -> raise NoMatch
      end
    | psi, T.Dot (T.Prg p1_, t1), T.Dot (T.Prg p2_, t2) -> begin
        matchSub (psi, t1, t2);
        matchPrg (psi, p1_, p2_)
      end
    | psi, T.Dot (T.Prg p1_, t1), T.Dot (T.Idx k, t2) -> begin
        matchSub (psi, t1, t2);
        matchPrg (psi, p1_, T.Var k)
      end
    | psi, T.Dot (T.Idx k, t1), T.Dot (T.Prg p2_, t2) -> begin
        matchSub (psi, t1, t2);
        matchPrg (psi, T.Var k, p2_)
      end
    | psi, T.Dot (T.Idx k1, t1), T.Dot (T.Idx k2, t2) ->
        begin if k1 = k2 then matchSub (psi, t1, t2) else raise NoMatch
        end
    | psi, T.Dot (T.Idx k, t1), T.Dot (T.Block (I.LVar (r, s1, (c, s2))), t2) ->
        let s1' = Whnf.invert s1 in
        ignore (r := Some (I.blockSub (I.Bidx k, s1')));
        matchSub (psi, t1, t2)
    | psi, T.Dot (T.Block b_, t1), T.Dot (T.Block (I.LVar (r, s1, (c, s2))), t2)
      ->
        let s1' = Whnf.invert s1 in
        ignore (r := Some (I.blockSub (b_, s1')));
        matchSub (psi, t1, t2)
  (* By Invariant *)

  and evalRedex = function
    | psi, v_, (T.Nil, _) -> v_
    | psi, v_, (T.SClo (s_, t1), t2) ->
        evalRedex (psi, v_, (s_, T.comp (t1, t2)))
    | psi, T.Lam (T.UDec (I.Dec (_, a_)), p'_), (T.AppExp (u_, s_), t) ->
        let v_ =
          evalPrg (psi, (p'_, T.Dot (T.Exp (I.EClo (u_, T.coerceSub t)), T.id)))
        in
        evalRedex (psi, v_, (s_, t))
    | psi, T.Lam (T.UDec _, p'_), (T.AppBlock (b_, s_), t) ->
        evalRedex
          ( psi,
            evalPrg
              ( psi,
                (p'_, T.Dot (T.Block (I.blockSub (b_, T.coerceSub t)), T.id)) ),
            (s_, t) )
    | psi, T.Lam (T.PDec _, p'_), (T.AppPrg (p_, s_), t) ->
        let v_ = evalPrg (psi, (p_, t)) in
        let v'_ = evalPrg (psi, (p'_, T.Dot (T.Prg v_, T.id))) in
        evalRedex (psi, v'_, (s_, t))

  (* raisePrg is used in handling of NEW construct
   raisePrg (G, P, F) = (P', F'))

       Invariant:
       If   Psi, G |- P in F
       and  Psi |- G : blockctx
       then Psi |- P' in F'
       and  P = raise (G, P')   (using subordination)
       and  F = raise (G, F')   (using subordination)
*)
  (* evalPrg (Psi, (P, t)) = V

       Invariant:
       If   Psi' |- P :: F
       and  Psi |- t :: Psi'
       and  |- Psi ctx[block]
       and  Psi |- P :: F'
       and  Psi |- P[t] evalsto V
       and  Psi |- F[t] == F'
    *)
  (* other cases should not occur -cs *)
  (* match is used to handle Case statements
  match (Psi, t1, O) = V

       Invariant:
       If   Psi |- t1 :: Psi''
       and  Psi'' |- O :: F
       and  |- Psi ctx[block]
       then if t1 matches O then Psi |- t ~ O evalPrgs to W
            otherwise exception NoMatch is raised.
    *)
  (* What do you want to do if it doesn't match anything *)
  (* can't happen when total function - ABP *)
  (* | match (Psi, t1, T.Cases Nil) = raise Domain  *)
  (* createVarSub (Psi, Psi') = t

       Invariant:
       If   |- Psi ctx[block]
       and  |- Psi' ctx
       then Psi |- t :: Psi'
    *)
  (* matchSub (t1, t2) = ()

       Invariant:
       If   Psi  |- t1 :: Psi'
       and  Psi  |- t2 :: Psi'
       and  Psi  |- t1 == t2 :: Psi'
       and  |- Psi ctx [block]
       then function returns ()
            otherwise exception NoMatch is raised
    *)
  (* evalRedex (Psi, V, (S, t)) = V'

       Invariant:
       If   Psi  |- V :: F1
       and  Psi' |- S :: F2 > F3
       and  Psi  |- t :: Psi'
       and  Psi' |- F1 == F2[t]
       and  |- Psi ctx[block]
       and  Psi |- P :: F'
       and  Psi |- V . (S[t]) evalsto V''
       then Psi |- V' == V'' : F3[t]
    *)
  (* topLevel (Psi, d, (P, t))

       Invariant:
       Psi |- t : Psi'
       Psi' |- P :: F
       d = | Psi' |

    *)
  let rec topLevel = function
    | psi, d, (T.Unit, t) -> ()
    | psi, d, (T.Let (d'_, p1_, T.Case cs_), t) ->
        let rec printLF arg__1 arg__2 =
          begin match (arg__1, arg__2) with
          | (_, _, _), 0 -> ()
          | (g_, I.Dot (I.Exp u_, s'), I.Decl (g'_, I.Dec (Some name, v_))), k
            ->
              ignore (printLF (g_, s', g'_) (k - 1));
              print
                (((((("def " ^ name) ^ " = ") ^ Print.expToString (g_, u_))
                  ^ " : ")
                 ^ Print.expToString (g_, I.EClo (v_, s')))
                ^ "\n")
          end
        in
        let match_ (psi, t1, T.Cases ((psi', t2, p_) :: c_)) =
          let t = createVarSub (psi, psi') in
          let t' = T.comp (t2, t) in
          let m = I.ctxLength psi' in
          ignore (matchSub (psi, t1, t'));
          let t'' = t in
          let _ =
            printLF (T.coerceCtx psi, T.coerceSub t'', T.coerceCtx psi') (m - d)
          in
          topLevel (psi, m, (p_, t''))
          (* Psi |- t : Psi' *)
          (* Psi' |- t2 . shift(k) : Psi'' *)
          (* T.normalizeSub *)
          (* Psi |- t'' : Psi' *)
        in
        let v_ = evalPrg (psi, (p1_, t)) in
        let v'_ = match_ (psi, T.Dot (T.Prg v_, t), cs_) in
        v'_
        (* printLF (G, s, G') k = ()
             Invariant:
             G |- s : G'
          *)
    | ( psi,
        d,
        ( T.Let
            ( d_,
              T.Lam ((T.UDec (I.BDec (Some name, (cid, s))) as d'_), p1_),
              p2_ ),
          t ) ) ->
        ignore (print (("new " ^ name) ^ "\n"));
        let d''_ = T.decSub (d'_, t) in
        ignore (topLevel (I.Decl (psi, d''_), d + 1, (p1_, T.dot1 t)));
        ()
    | psi, d, (T.Let (d_, p1_, p2_), t) ->
        let (T.PDec (Some name, f_, _, _)) = d_ in
        let v_ = evalPrg (psi, (p1_, t)) in
        let _ =
          print
            (((((("val " ^ name) ^ " = ") ^ TomegaPrint.prgToString (psi, v_))
              ^ " :: ")
             ^ TomegaPrint.forToString (psi, f_))
            ^ "\n")
        in
        let v'_ = topLevel (psi, d + 1, (p2_, T.Dot (T.Prg v_, t))) in
        v'_

  (* function definition *)
  (* new declaration *)
  (* lf value definition *)

  (* in -- removed local *)
  let evalPrg = function p_ -> evalPrg (I.Null, (p_, T.id))
  let topLevel = function p_ -> topLevel (I.Null, 0, (p_, T.id))
end
(* end -- removed local *)
(* # 1 "src/tomega/Opsem.sml.ml" *)
