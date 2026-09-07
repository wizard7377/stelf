open! Intsyn
open! Intsyn.Lambda_
open! Names.Names_
open! Print.Print_
open! Typecheck.Typecheck_

(* # 1 "src/tomega/Opsem.sig.ml" *)
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
  let rec matchPrg (psi, p1, p2) =
    matchVal (psi, (p1, T.id), T.normalizePrg p2 T.id)

  and matchVal = function
    | psi, (T.Unit, _), T.Unit -> ()
    | psi, (T.PairPrg (p1, p1'), t1), T.PairPrg (p2, p2') -> begin
        matchVal (psi, (p1, t1), p2);
        matchVal (psi, (p1', t1), p2')
      end
    | psi, (T.PairBlock (b1, p1), t1), T.PairBlock (b2, p2) -> begin
        matchVal (psi, (p1, t1), p2);
        try
          Unify.unifyBlock
            (T.coerceCtx psi) (I.blockSub b1 (T.coerceSub t1)) b2
        with Unify.Unify _ -> raise NoMatch
      end
    | psi, (T.PairExp (u1, p1), t1), T.PairExp (u2, p2) -> begin
        matchVal (psi, (p1, t1), p2);
        try Unify.unify (T.coerceCtx psi) (u1, T.coerceSub t1) (u2, I.id)
        with Unify.Unify _ -> raise NoMatch
      end
    | psi, (T.PClo (p, t1'), t1), pt ->
        matchVal (psi, (p, T.comp t1' t1), pt)
    | psi, (p', t1), T.PClo (T.PClo (p, t2), t3) ->
        matchVal (psi, (p', t1), T.PClo (p, T.comp t2 t3))
    | ( psi,
        (p', t1),
        T.PClo (T.EVar (_, ({ contents = None } as r), _, _, _, _), t2) ) ->
        let iw = T.invertSub t2 in
        r := Some (T.PClo (p', T.comp t1 iw))
        (* ABP -- just make sure this is right *)
    | psi, (p', t1), T.EVar (_, ({ contents = None } as r), _, _, _, _) ->
        r := Some (T.PClo (p', t1))
    | psi, (v, t), T.EVar (d, ({ contents = Some p } as r), f, _, _, _) ->
        matchVal (psi, (v, t), p)
    | _ -> raise NoMatch

  (* ABP -- this should never occur, since we normalized it to start *)
  (* ABP -- Do we need this? I added it *)
  (* Added by ABP *)

  (* ABP -- normalizePrg invariant does not state what happens to non-free EVArs,
       and there are some embedded under PClo... *)
  let rec append (g1, a) = match a with
    | I.Null -> g1
    | I.Decl (g2, d) -> I.Decl (append (g1, g2), d)

  and raisePrg a1 b1 c1 = match a1, b1, c1 with
    | psi, g, T.Unit -> T.Unit
    | psi, g, T.PairPrg (p1, p2) ->
        let p1' = raisePrg psi g p1 in
        let p2' = raisePrg psi g p2 in
        T.PairPrg (p1', p2')
    | psi, g, T.PairExp (u, p) ->
        let v = TypeCheck.infer' (append (T.coerceCtx psi, g)) u in
        let w = S.weaken g (I.targetFam v) in
        let iw = Whnf.invert w in
        let g' = Whnf.strengthen iw g in
        let u' = A.raiseTerm g' (I.EClo (u, iw)) in
        let p' = raisePrg psi g p in
        T.PairExp (u', p')
  (* this is a real time sink, it would be much better if we did not have to
      compute the type information of U,
      more thought is required
   *)

  (* G  |- w  : G'    *)
  (* G' |- iw : G     *)
  (* Psi0, G' |- B'' ctx *)
  and evalPrg (psi, a) = match a with
    | (T.Unit, t) -> T.Unit
    | (T.PairExp (m, p), t) ->
        T.PairExp (I.EClo (m, T.coerceSub t), evalPrg (psi, (p, t)))
    | (T.PairBlock (b, p), t) ->
        T.PairBlock (I.blockSub b (T.coerceSub t), evalPrg (psi, (p, t)))
    | (T.PairPrg (p1, p2), t) ->
        T.PairPrg (evalPrg (psi, (p1, t)), evalPrg (psi, (p2, t)))
    | (T.Redex (p, s), t) ->
        evalRedex (psi, evalPrg (psi, (p, t)), (s, t))
    | (T.Var k, t) ->
        begin match T.varSub k t with T.Prg p -> evalPrg (psi, (p, T.id))
        end
    | (T.Const lemma, t) -> evalPrg (psi, (T.lemmaDef lemma, t))
    | (T.Lam ((T.UDec (I.BDec _) as d), p), t) ->
        let d' = T.decSub d t in
        T.Lam (d', evalPrg (I.Decl (psi, d'), (p, T.dot1 t)))
    | (T.Lam (d, p), t) -> T.Lam (T.decSub d t, T.PClo (p, T.dot1 t))
    | ((T.Rec (d, p) as p'), t) ->
        evalPrg (psi, (p, T.Dot (T.Prg (T.PClo (p', t)), t)))
    | (T.PClo (p, t'), t) -> evalPrg (psi, (p, T.comp t' t))
    | (T.Case (T.Cases o), t') -> match_ (psi, t', T.Cases (rev o))
    | (T.EVar (d, ({ contents = Some p } as r), f, _, _, _), t) ->
        evalPrg (psi, (p, t))
    | (T.Let (d, p1, p2), t) ->
        let v = evalPrg (psi, (p1, t)) in
        let v' = evalPrg (psi, (p2, T.Dot (T.Prg v, t))) in
        v'
    | (T.New (T.Lam (d, p)), t) ->
        let d' = T.decSub d t in
        let (T.UDec d'') = d' in
        let d''' = T.UDec (Names.decName (T.coerceCtx psi) d'') in
        let v = evalPrg (I.Decl (psi, d'''), (p, T.dot1 t)) in
        let b = T.coerceCtx (I.Decl (I.Null, d''')) in
        let g, t' = T.deblockify b in
        let newP = raisePrg psi g (T.normalizePrg v t') in
        newP
        (* unnecessary naming, remove later --cs *)
    | (T.Box (w, p), t) -> evalPrg (psi, (p, t))
    | (T.Choose p, t) ->
        let rec substToSpine' (a, b, t_acc) = match a, b with
          | I.Shift n, I.Null -> t_acc
          | I.Shift n, (I.Decl _ as g) ->
              substToSpine' (I.Dot (I.Idx (n + 1), I.Shift (n + 1)), g, t_acc)
          | I.Dot (I.Exp u, s), I.Decl (g, v) ->
              substToSpine' (s, g, T.AppExp (u, t_acc))
          | I.Dot (I.Idx n, s), I.Decl (g, I.Dec (_, v)) ->
              let us, _ =
                Whnf.whnfEta (I.Root (I.BVar n, I.Nil), I.id) (v, I.id)
              in
              substToSpine'
                ( s,
                  g,
                  let u_eta, s_eta = us in
                  T.AppExp (I.EClo (u_eta, s_eta), t_acc) )
          (* Eta-expand *)
        in
        let rec choose (k, a) = match a with
          | I.Null -> raise Abort
          | I.Decl (psi', T.PDec _) -> choose (k + 1, psi')
          | I.Decl (psi', T.UDec (I.Dec _)) -> choose (k + 1, psi')
          | I.Decl (psi', T.UDec (I.BDec (_, (l1, s1)))) -> (
              let gsome, gpi = I.constBlock l1 in
              let s =
                substToSpine' (s1, gsome, T.AppBlock (I.Bidx k, T.Nil))
              in
              try evalPrg (psi, (T.Redex (T.PClo (p, t), s), T.id))
              with Abort -> choose (k + 1, psi'))
        in
        choose (1, psi)
  (* This function was imported from Cover.fun. *)

  and match_ (psi, t1, a) = match a with
    | T.Cases ((psi', t2, p) :: c) -> (
        let t = createVarSub psi psi' in
        let t' = T.comp t2 t in
        try
          begin
            matchSub psi t1 t';
            evalPrg (psi, (p, t) (*T.normalizeSub*))
          end
        with NoMatch -> match_ (psi, t1, T.Cases c)
        (* val I.Null = Psi *)
        (* Psi |- t : Psi' *)
        (* Psi' |- t2 . shift(k) : Psi'' *)
        (* Note that since we are missing the shift(k), it is possible
           * that t' has extra DOTs in there that weren't removed *)
        )
    | T.Cases [] -> raise Abort

  and createVarSub a1 b1 = match a1, b1 with
    | psi, I.Null -> T.Shift (I.ctxLength psi)
    | psi, (I.Decl (psi', T.PDec (name, f, None, None)) as psi'') ->
        let t = createVarSub psi psi' in
        let t' =
          T.Dot (T.Prg (T.newEVarTC psi (T.forSub f t) None None), t)
        in
        t'
    | psi, I.Decl (psi', T.UDec (I.Dec (name, v))) ->
        let t = createVarSub psi psi' in
        T.Dot
          ( T.Exp
              (I.EVar
                 (ref None, T.coerceCtx psi, I.EClo (v, T.coerceSub t), ref [])),
            t )
    | psi, I.Decl (psi', T.UDec (I.BDec (name, (cid, s)))) ->
        let t = createVarSub psi psi' in
        T.Dot
          ( T.Block (I.LVar (ref None, I.id, (cid, I.comp s (T.coerceSub t)))),
            t )

  and matchSub a1 b1 c1 = match a1, b1, c1 with
    | psi, _, T.Shift _ -> ()
    | psi, T.Shift n, (T.Dot _ as t) ->
        matchSub psi (T.Dot (T.Idx (n + 1), T.Shift (n + 1))) t
    | psi, T.Dot (T.Exp u1, t1), T.Dot (T.Exp u2, t2) -> begin
        matchSub psi t1 t2;
        try Unify.unify (T.coerceCtx psi) (u1, I.id) (u2, I.id)
        with Unify.Unify s -> raise NoMatch
      end
    | psi, T.Dot (T.Exp u1, t1), T.Dot (T.Idx k, t2) -> begin
        matchSub psi t1 t2;
        try
          Unify.unify
            (T.coerceCtx psi) (u1, I.id) (I.Root (I.BVar k, I.Nil), I.id)
        with Unify.Unify _ -> raise NoMatch
      end
    | psi, T.Dot (T.Idx k, t1), T.Dot (T.Exp u2, t2) -> begin
        matchSub psi t1 t2;
        try
          Unify.unify
            (T.coerceCtx psi) (I.Root (I.BVar k, I.Nil), I.id) (u2, I.id)
        with Unify.Unify _ -> raise NoMatch
      end
    | psi, T.Dot (T.Prg p1, t1), T.Dot (T.Prg p2, t2) -> begin
        matchSub psi t1 t2;
        matchPrg (psi, p1, p2)
      end
    | psi, T.Dot (T.Prg p1, t1), T.Dot (T.Idx k, t2) -> begin
        matchSub psi t1 t2;
        matchPrg (psi, p1, T.Var k)
      end
    | psi, T.Dot (T.Idx k, t1), T.Dot (T.Prg p2, t2) -> begin
        matchSub psi t1 t2;
        matchPrg (psi, T.Var k, p2)
      end
    | psi, T.Dot (T.Idx k1, t1), T.Dot (T.Idx k2, t2) ->
        begin if k1 = k2 then matchSub psi t1 t2 else raise NoMatch
        end
    | psi, T.Dot (T.Idx k, t1), T.Dot (T.Block (I.LVar (r, s1, (c, s2))), t2) ->
        let s1' = Whnf.invert s1 in
        ignore (r := Some (I.blockSub (I.Bidx k) s1'));
        matchSub psi t1 t2
    | psi, T.Dot (T.Block b, t1), T.Dot (T.Block (I.LVar (r, s1, (c, s2))), t2)
      ->
        let s1' = Whnf.invert s1 in
        ignore (r := Some (I.blockSub b s1'));
        matchSub psi t1 t2
  (* By Invariant *)

  and evalRedex (psi, a, b) = match a, b with
    | v, (T.Nil, _) -> v
    | v, (T.SClo (s, t1), t2) ->
        evalRedex (psi, v, (s, T.comp t1 t2))
    | T.Lam (T.UDec (I.Dec (_, a)), p'), (T.AppExp (u, s), t) ->
        let v =
          evalPrg (psi, (p', T.Dot (T.Exp (I.EClo (u, T.coerceSub t)), T.id)))
        in
        evalRedex (psi, v, (s, t))
    | T.Lam (T.UDec _, p'), (T.AppBlock (b, s), t) ->
        evalRedex
          ( psi,
            evalPrg
              ( psi,
                (p', T.Dot (T.Block (I.blockSub b (T.coerceSub t)), T.id)) ),
            (s, t) )
    | T.Lam (T.PDec _, p'), (T.AppPrg (p, s), t) ->
        let v = evalPrg (psi, (p, t)) in
        let v' = evalPrg (psi, (p', T.Dot (T.Prg v, T.id))) in
        evalRedex (psi, v', (s, t))

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
  let rec topLevel (psi, d, a) = match a with
    | (T.Unit, t) -> ()
    | (T.Let (d', p1, T.Case cs), t) ->
        let rec printLF arg__1 arg__2 =
          begin match (arg__1, arg__2) with
          | (_, _, _), 0 -> ()
          | (g, I.Dot (I.Exp u, s'), I.Decl (g', I.Dec (Some name, v))), k
            ->
              ignore (printLF (g, s', g') (k - 1));
              print
                (((((("def " ^ name) ^ " = ") ^ Print.expToString g u)
                  ^ " : ")
                 ^ Print.expToString g (I.EClo (v, s')))
                ^ "\n")
          end
        in
        let match_ (psi, t1, T.Cases ((psi', t2, p) :: c)) =
          let t = createVarSub psi psi' in
          let t' = T.comp t2 t in
          let m = I.ctxLength psi' in
          ignore (matchSub psi t1 t');
          let t'' = t in
          ignore (printLF (T.coerceCtx psi, T.coerceSub t'', T.coerceCtx psi') (m - d));
          topLevel (psi, m, (p, t''))
          (* Psi |- t : Psi' *)
          (* Psi' |- t2 . shift(k) : Psi'' *)
          (* T.normalizeSub *)
          (* Psi |- t'' : Psi' *)
        in
        let v = evalPrg (psi, (p1, t)) in
        let v' = match_ (psi, T.Dot (T.Prg v, t), cs) in
        v'
        (* printLF (G, s, G') k = ()
             Invariant:
             G |- s : G'
          *)
    | ( T.Let
            ( d_,
              T.Lam ((T.UDec (I.BDec (Some name, (cid, s))) as d'), p1),
              p2 ),
          t ) ->
        ignore (print (("new " ^ name) ^ "\n"));
        let d'' = T.decSub d' t in
        ignore (topLevel (I.Decl (psi, d''), d + 1, (p1, T.dot1 t)));
        ()
    | (T.Let (d_, p1, p2), t) ->
        let (T.PDec (Some name, f, _, _)) = d_ in
        let v = evalPrg (psi, (p1, t)) in
        ignore (print
            (((((("val " ^ name) ^ " = ") ^ TomegaPrint.prgToString psi v)
              ^ " :: ")
             ^ TomegaPrint.forToString psi f)
            ^ "\n"));
        let v' = topLevel (psi, d + 1, (p2, T.Dot (T.Prg v, t))) in
        v'

  (* function definition *)
  (* new declaration *)
  (* lf value definition *)

  (* in -- removed local *)
  let evalPrg = function p -> evalPrg (I.Null, (p, T.id))
  let topLevel = function p -> topLevel (I.Null, 0, (p, T.id))
end
(* end -- removed local *)
(* # 1 "src/tomega/Opsem.sml.ml" *)
