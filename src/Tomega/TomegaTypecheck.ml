open! Intsyn
open! Intsyn.Lambda_
open! Print.Print_
open! Typecheck.Typecheck_
open! Meta

(* # 1 "src/tomega/TomegaTypecheck.sig.ml" *)
module Tomega = Lambda_.Tomega

(* Type checking for functional proof term calculus *)
(* Author: Carsten Schuermann *)
(* Modified: Yu Liao *)
include TOMEGATYPECHECK
(* Signature TOMEGATYPECHECK *)

(* # 1 "src/tomega/TomegaTypecheck.fun.ml" *)
open! Basis

exception Error of string

let () =
  Printexc.register_printer (function Error msg -> Some msg | _ -> None)

module TomegaTypeCheck (TomegaTypeCheck__0 : sig
  (* Type checking for Tomega *)
  (* Author: Carsten Schuermann *)
  (* Modified: Yu Liao *)
  module Abstract : ABSTRACT
  module TypeCheck : TYPECHECK
  module Conv : CONV
  module Whnf : WHNF
  module Print : PRINT
  module TomegaPrint : Tomegaprint.TOMEGAPRINT
  module Subordinate : Subordinate.Subordinate_.SUBORDINATE
  module Weaken : WEAKEN.WEAKEN
  module TomegaAbstract : TOMEGAABSTRACT.TOMEGAABSTRACT
end) : TOMEGATYPECHECK = struct
  (*! structure IntSyn = IntSyn' !*)
  (*! structure Tomega = Tomega' !*)
  exception Error = Error

  open! struct
    module I = IntSyn
    module T = Tomega
    module S = Subordinate
    module TA = TomegaTypeCheck__0.TomegaAbstract

    let chatter chlev f = Display.chatter_s chlev (f ())

    let normalizeHead (a, t) = match a with
      | T.Const lemma -> T.Const lemma
      | T.Var k ->
          begin match T.varSub k t with T.Idx k' -> T.Var k'
          end

    let rec inferSpine (psi, s, (f, t)) = inferSpineW (psi, s, T.whnfFor f t)

    and inferSpineW (psi, a, b) = match a, b with
      | T.Nil, (f, t) -> (f, t)
      | T.AppExp (m, s), (T.All ((T.UDec (I.Dec (_, a)), _), f), t) ->
          ignore (chatter 4 (function () -> "[appExp"));
          let g = T.coerceCtx psi in
          ignore (TypeCheck.typeCheck g (m, I.EClo (a, T.coerceSub t)));
          ignore (chatter 4 (function () -> "]"));
          inferSpine (psi, s, (f, T.Dot (T.Exp m, t)))
      | T.AppBlock (I.Bidx k, s_), (T.All ((T.UDec (I.BDec (_, (cid, s))), _), f2), t2) ->
          let (T.UDec (I.BDec (_, (cid', s')))) = T.ctxDec psi k in
          let g', _ = I.conDecBlock (I.sgnLookup cid') in
          ignore begin if cid <> cid' then raise (Error "Block label incompatible")
            else ()
            end;
          let s'' = T.coerceSub (T.comp (T.embedSub s) t2) in
          ignore (Conv.convSub s' s'');
          inferSpine (psi, s_, (f2, T.Dot (T.Block (I.Bidx k), t2)))
      | T.AppPrg (p, s), (T.All ((T.PDec (_, f1, _, _), _), f2), t) ->
          ignore (checkPrg psi (p, (f1, t)));
          inferSpine (psi, s, (f2, T.dot1 t))
      | _, _ -> raise (Error "applied, but not of function type.")

    and inferPrg (psi, a) = match a with
      | T.Lam (d, p) ->
          let f = inferPrg (I.Decl (psi, d), p) in
          T.All ((d, T.Explicit), f)
      | T.New p ->
          let (T.All ((T.UDec (I.BDec _ as d), _), f)) = inferPrg (psi, p) in
          TA.raiseF (I.Decl (I.Null, d)) (f, I.id)
      | T.PairExp (u, p) ->
          let v = TypeCheck.infer' (T.coerceCtx psi) u in
          let f = inferPrg (psi, p) in
          T.Ex ((I.Dec (None, v), T.Explicit), f)
      | T.PairBlock (I.Bidx k, p) ->
          let d = I.ctxLookup (T.coerceCtx psi) k in
          let f = inferPrg (psi, p) in
          T.Ex ((d, T.Explicit), f)
      | T.PairPrg (p1, p2) ->
          let f1 = inferPrg (psi, p1) in
          let f2 = inferPrg (psi, p2) in
          T.And (f1, f2)
      | Unit -> T.True
      | T.Var k ->
          begin match T.ctxDec psi k with T.PDec (_, f', _, _) -> f'
          end
      | T.Const c -> inferLemma c
      | T.Redex (p, s) ->
          let f1 = inferPrg (psi, p) in
          let f2 = inferSpine (psi, s, (f1, T.id)) in
          (let f__, t__ = f2 in T.forSub f__ t__)
      | T.Rec ((T.PDec (_, f, _, _) as d), p) ->
          ignore (checkPrg (I.Decl (psi, d)) (p, (f, T.id)));
          f
      | T.Let ((T.PDec (_, f1, _, _) as d), p1, p2) ->
          ignore (checkPrg psi (p1, (f1, T.id)));
          let f2 = inferPrg (I.Decl (psi, d), p2) in
          f2

    and checkPrg psi (p, (f, t)) = checkPrgW (psi, (p, T.whnfFor f t))

    and checkPrgW (psi, a) = match a with
      | (Unit, (True, _)) ->
          ignore (chatter 4 (function () -> "[true]"));
          ()
      | (T.Const lemma, (f, t)) ->
          convFor (psi, (inferLemma lemma, T.id), (f, t))
      | (T.Var k, (f, t)) ->
          begin match T.ctxDec psi k with
          | T.PDec (_, f', _, _) -> convFor (psi, (f', T.id), (f, t))
          end
      | ( T.Lam ((T.PDec (x, f1, _, _) as d), p),
            (T.All ((T.PDec (x', f1', _, _), _), f2), t) ) ->
          ignore (chatter 4 (function () -> "[lam[p]"));
          ignore (convFor (psi, (f1, T.id), (f1', t)));
          ignore (chatter 4 (function () -> "]"));
          checkPrg (I.Decl (psi, d)) (p, (f2, T.dot1 t))
      | (T.Lam (T.UDec d, p), (T.All ((T.UDec d', _), f), t2)) ->
          ignore (chatter 4 (function () -> "[lam[u]"));
          ignore (Conv.convDec d I.id (d', T.coerceSub t2));
          ignore (chatter 4 (function () -> "]"));
          checkPrg (I.Decl (psi, T.UDec d)) (p, (f, T.dot1 t2))
      | (T.PairExp (m, p), (T.Ex ((I.Dec (x, a), _), f2), t)) ->
          ignore (chatter 4 (function () -> "[pair [e]"));
          let g = T.coerceCtx psi in
          ignore (TypeCheck.typeCheck g (m, I.EClo (a, T.coerceSub t)));
          ignore (chatter 4 (function () -> "]"));
          checkPrg psi (p, (f2, T.Dot (T.Exp m, t)))
      | ( T.PairBlock (I.Bidx k, p),
            (T.Ex ((I.BDec (_, (cid, s)), _), f2), t) ) ->
          let (T.UDec (I.BDec (_, (cid', s')))) = T.ctxDec psi k in
          let g', _ = I.conDecBlock (I.sgnLookup cid) in
          ignore begin if cid' <> cid then raise (Error "Block label mismatch")
            else ()
            end;
          ignore (convSub
              (psi, T.embedSub s', T.comp (T.embedSub s) t, T.revCoerceCtx g'));
          checkPrg psi (p, (f2, T.Dot (T.Block (I.Bidx k), t)))
      | (T.PairPrg (p1, p2), (T.And (f1, f2), t)) ->
          ignore (chatter 4 (function () -> "[and"));
          ignore (checkPrg psi (p1, (f1, t)));
          ignore (chatter 4 (function () -> "..."));
          ignore (checkPrg psi (p2, (f2, t)));
          ignore (chatter 4 (function () -> "]"));
          ()
      | (T.Case omega, ft) -> checkCases (psi, (omega, ft))
      | (T.Rec ((T.PDec (x, f, _, _) as d), p), (f', t)) ->
          ignore (chatter 4 (function () -> "[rec"));
          ignore (convFor (psi, (f, T.id), (f', t)));
          ignore (chatter 4 (function () -> "]\n"));
          checkPrg (I.Decl (psi, d)) (p, (f', t))
      | (T.Let ((T.PDec (_, f1, _, _) as d), p1, p2), (f2, t)) ->
          ignore (chatter 4 (function () -> "[let"));
          ignore (checkPrg psi (p1, (f1, T.id)));
          ignore (chatter 4 (function () -> "."));
          ignore (checkPrg (I.Decl (psi, d)) (p2, (f2, T.comp t T.shift)));
          ignore (chatter 4 (function () -> "]\n"));
          ()
      | ( T.New (T.Lam (T.UDec (I.BDec (_, (cid, s)) as d), p) as p'),
            (f, t) ) ->
          ignore (chatter 5 (function () -> "[new1..."));
          let (T.All ((T.UDec d'', _), f')) = inferPrg (psi, p') in
          ignore (chatter 5 (function () -> "][new2..."));
          let f'' = TA.raiseF (I.Decl (I.Null, d)) (f', I.id) in
          convFor (psi, (f'', T.id), (f, t));
          chatter 5 (function () -> "]\n")
      | (T.Redex (p1, s2), (f, t)) ->
          let f' = inferPrg (psi, p1) in
          checkSpine (psi, s2, (f', T.id), (f, t))
      | (T.Box (w, p), (T.World (w', f), t)) ->
          checkPrgW (psi, (p, (f, t)))

    and checkSpine (psi, a, b, c) = match a, b, c with
      | T.Nil, (f, t), (f', t') -> convFor (psi, (f, t), (f', t'))
      | T.AppExp (u, s), (T.All ((T.UDec (I.Dec (_, v)), _), f), t), (f', t') -> begin
          TypeCheck.typeCheck (T.coerceCtx psi) (u, I.EClo (v, T.coerceSub t));
          checkSpine (psi, s, (f, T.Dot (T.Exp u, t)), (f', t'))
        end
      | T.AppPrg (p, s), (T.All ((T.PDec (_, f1, _, _), _), f2), t), (f', t') -> begin
          checkPrgW (psi, (p, (f1, t)));
          checkSpine (psi, s, (f2, T.Dot (T.Undef, t)), (f', t'))
        end
      | T.AppExp (u, s), (T.FClo (f, t1), t), (f', t') ->
          checkSpine (psi, T.AppExp (u, s), (f, T.comp t1 t), (f', t'))

    and checkCases (psi, a) = match a with
      | (T.Cases [], (f2, t2)) -> ()
      | (T.Cases ((psi', t', p) :: omega), (f2, t2)) ->
          ignore (chatter 4 (function () -> "[case... "));
          ignore (chatter 4 (function () -> "sub... "));
          ignore (checkSub psi' t' psi);
          ignore (chatter 4 (function () -> "prg... "));
          let t2' = T.comp t2 t' in
          ignore (checkCtx psi);
          ignore (checkCtx psi');
          ignore (chatter 4 (function () -> "]"));
          ignore (checkPrg psi' (p, (f2, t2')));
          ignore (chatter 4 (function () -> "]\n"));
          ignore (checkCases (psi, (T.Cases omega, (f2, t2))));
          ()

    and inferLemma lemma =
      begin match T.lemmaLookup lemma with
      | T.ForDec (_, f) -> f
      | T.ValDec (_, _, f) -> f
      end

    and convFor (psi, (f1, t1), (f2, t2)) = convForW (psi, T.whnfFor f1 t1, T.whnfFor f2 t2)

    and convForW = function
      | _, (T.True, _), (T.True, _) -> ()
      | ( psi,
          (T.All (((T.UDec (I.Dec (_, a1)) as d), _), f1), t1),
          (T.All ((T.UDec (I.Dec (_, a2)), _), f2), t2) ) ->
          let g = T.coerceCtx psi in
          let s1 = T.coerceSub t1 in
          let s2 = T.coerceSub t2 in
          ignore (Conv.conv (a1, s1) (a2, s2));
          ignore (TypeCheck.typeCheck g (I.EClo (a1, s1), I.Uni I.Type));
          ignore (TypeCheck.typeCheck g (I.EClo (a2, s2), I.Uni I.Type));
          let d' = T.decSub d t1 in
          ignore (convFor (I.Decl (psi, d'), (f1, T.dot1 t1), (f2, T.dot1 t2)));
          ()
      | ( psi,
          (T.All (((T.UDec (I.BDec (_, (l1, s1))) as d), _), f1), t1),
          (T.All ((T.UDec (I.BDec (_, (l2, s2))), _), f2), t2) ) ->
          ignore begin if l1 <> l2 then raise (Error "Contextblock clash") else ()
            end;
          let g', _ = I.conDecBlock (I.sgnLookup l1) in
          ignore (convSub
              ( psi,
                T.comp (T.embedSub s1) t1,
                T.comp (T.embedSub s2) t2,
                T.embedCtx g' ));
          let d' = T.decSub d t1 in
          ignore (convFor (I.Decl (psi, d'), (f1, T.dot1 t1), (f2, T.dot1 t2)));
          ()
      | ( psi,
          (T.Ex (((I.Dec (_, a1) as d), _), f1), t1),
          (T.Ex ((I.Dec (_, a2), _), f2), t2) ) ->
          let g = T.coerceCtx psi in
          let s1 = T.coerceSub t1 in
          let s2 = T.coerceSub t2 in
          ignore (Conv.conv (a1, s1) (a2, s2));
          ignore (TypeCheck.typeCheck g (I.EClo (a1, s1), I.Uni I.Type));
          ignore (TypeCheck.typeCheck g (I.EClo (a2, s2), I.Uni I.Type));
          let d' = I.decSub d s1 in
          ignore (convFor
              (I.Decl (psi, T.UDec d'), (f1, T.dot1 t1), (f2, T.dot1 t2)));
          ()
      | ( psi,
          (T.Ex (((I.BDec (name, (l1, s1)) as d), _), f1), t1),
          (T.Ex ((I.BDec (_, (l2, s2)), _), f2), t2) ) ->
          ignore begin if l1 <> l2 then raise (Error "Contextblock clash") else ()
            end;
          let g', _ = I.conDecBlock (I.sgnLookup l1) in
          let s1 = T.coerceSub t1 in
          ignore (convSub
              ( psi,
                T.comp (T.embedSub s1) t1,
                T.comp (T.embedSub s2) t2,
                T.embedCtx g' ));
          let d' = I.decSub d s1 in
          ignore (convFor
              (I.Decl (psi, T.UDec d'), (f1, T.dot1 t1), (f2, T.dot1 t2)));
          ()
      | psi, (T.And (f1, f1'), t1), (T.And (f2, f2'), t2) ->
          ignore (convFor (psi, (f1, t1), (f2, t2)));
          ignore (convFor (psi, (f1', t1), (f2', t2)));
          ()
      | ( psi,
          (T.All (((T.PDec (_, f1, _, _) as d), _), f1'), t1),
          (T.All ((T.PDec (_, f2, _, _), _), f2'), t2) ) ->
          ignore (convFor (psi, (f1, t1), (f2, t2)));
          let d' = T.decSub d t1 in
          ignore (convFor (I.Decl (psi, d'), (f1', T.dot1 t1), (f2', T.dot1 t2)));
          ()
      | psi, (T.World (w1, f1), t1), (T.World (w2, f2), t2) ->
          ignore (convFor (psi, (f1, t1), (f2, t2)));
          ()
      | _ -> raise (Error "Typecheck error")

    and convSub (g, a, b, c) = match a, b, c with
      | T.Shift k1, T.Shift k2, g' ->
          begin if k1 = k2 then () else raise (Error "Sub not equivalent")
          end
      | T.Shift k, (T.Dot _ as s2), g' ->
          convSub (g, T.Dot (T.Idx (k + 1), T.Shift (k + 1)), s2, g')
      | (T.Dot _ as s1), T.Shift k, g' ->
          convSub (g, s1, T.Dot (T.Idx (k + 1), T.Shift (k + 1)), g')
      | T.Dot (T.Idx k1, s1), T.Dot (T.Idx k2, s2), I.Decl (g', _) ->
          begin if k1 = k2 then convSub (g, s1, s2, g')
          else raise (Error "Sub not equivalent")
          end
      | T.Dot (T.Exp m1, s1), T.Dot (T.Exp m2, s2), I.Decl (g', T.UDec (I.Dec (_, a))) ->
          ignore (TypeCheck.checkConv m1 m2);
          ignore (TypeCheck.typeCheck (T.coerceCtx g) (m1, a));
          convSub (g, s1, s2, g')
      | T.Dot (T.Block (I.Bidx v1), s1), T.Dot (T.Block (I.Bidx v2), s2), I.Decl (g', T.UDec (I.BDec (_, (l, s)))) ->
          let (T.UDec (I.BDec (_, (l1, s11)))) = T.ctxDec g v1 in
          let (T.UDec (I.BDec (_, (l2, s22)))) = T.ctxDec g v2 in
          ignore begin if l1 = l2 then () else raise (Error "Sub not equivalent")
            end;
          ignore begin if l1 = l then () else raise (Error "Sub not equivalent")
            end;
          let g'', _ = I.conDecBlock (I.sgnLookup l) in
          ignore (convSub (g, T.embedSub s11, T.embedSub s22, T.revCoerceCtx g''));
          ignore (convSub (g, T.embedSub s11, T.embedSub s, T.revCoerceCtx g''));
          convSub (g, s1, s2, g')
      | T.Dot (T.Prg p1, s1), T.Dot (T.Prg p2, s2), I.Decl (g', T.PDec (_, f, _, _)) ->
          ignore (isValue p1);
          ignore (isValue p2);
          ignore (convValue (g, p1, p2, f));
          convSub (g, s1, s2, g')
      | T.Dot (T.Idx k1, s1), T.Dot (T.Exp m2, s2), I.Decl (g', T.UDec (I.Dec (_, a))) ->
          ignore (TypeCheck.checkConv (I.Root (I.BVar k1, I.Nil)) m2);
          ignore (TypeCheck.typeCheck (T.coerceCtx g) (m2, a));
          convSub (g, s1, s2, g')
      | T.Dot (T.Exp m1, s1), T.Dot (T.Idx k2, s2), I.Decl (g', T.UDec (I.Dec (_, a))) ->
          ignore (TypeCheck.checkConv m1 (I.Root (I.BVar k2, I.Nil)));
          ignore (TypeCheck.typeCheck (T.coerceCtx g) (m1, a));
          convSub (g, s1, s2, g')
      | T.Dot (T.Idx k1, s1), T.Dot (T.Prg p2, s2), I.Decl (g', T.PDec (_, f, _, _)) ->
          ignore (isValue p2);
          ignore (convValue (g, T.Var k1, p2, f));
          convSub (g, s1, s2, g')
      | T.Dot (T.Prg p1, s1), T.Dot (T.Idx k2, s2), I.Decl (g', T.PDec (_, f, _, _)) ->
          ignore (isValue p1);
          ignore (convValue (g, p1, T.Var k2, f));
          convSub (g, s1, s2, g')

    and convValue (g, p1, p2, f) = ()

    and checkFor a1 b1 = match a1, b1 with
      | psi, (T.True, _) -> ()
      | psi, (T.All (((T.PDec (_, f1, _, _) as d), _), f2), t) -> begin
          checkFor psi (f1, t);
          checkFor (I.Decl (psi, d)) (f2, T.dot1 t)
        end
      | psi, (T.All (((T.UDec d as d'), _), f), t) -> begin
          TypeCheck.checkDec (T.coerceCtx psi) (d, T.coerceSub t);
          checkFor (I.Decl (psi, d')) (f, T.dot1 t)
        end
      | psi, (T.Ex ((d, _), f), t) -> begin
          TypeCheck.checkDec (T.coerceCtx psi) (d, T.coerceSub t);
          checkFor (I.Decl (psi, T.UDec d)) (f, T.dot1 t)
        end
      | psi, (T.And (f1, f2), t) -> begin
          checkFor psi (f1, t);
          checkFor psi (f2, t)
        end
      | psi, (T.FClo (f, t'), t) -> checkFor psi (f, T.comp t' t)
      | psi, (T.World (w, f), t) -> checkFor psi (f, t)

    and checkCtx = function
      | I.Null -> ()
      | I.Decl (psi, T.UDec d) -> begin
          checkCtx psi;
          TypeCheck.checkDec (T.coerceCtx psi) (d, I.id)
        end
      | I.Decl (psi, T.PDec (_, f, _, _)) -> begin
          checkCtx psi;
          checkFor psi (f, T.id)
        end

    and checkSub a3 b3 c3 = match a3, b3, c3 with
      | I.Null, T.Shift 0, I.Null -> ()
      | I.Decl (g, d), T.Shift k, I.Null ->
          begin if k > 0 then checkSub g (T.Shift (k - 1)) I.Null
          else raise (Error "Sub is not well typed!")
          end
      | g, T.Shift k, g' ->
          checkSub g (T.Dot (T.Idx (k + 1), T.Shift (k + 1))) g'
      | g, T.Dot (T.Idx k, s'), I.Decl (g', T.UDec (I.Dec (_, a))) ->
          ignore (checkSub g s' g');
          let (T.UDec (I.Dec (_, a'))) = T.ctxDec g k in
          begin if Conv.conv (a', I.id) (a, T.coerceSub s') then ()
          else raise (Error "Sub isn't well typed!")
          end
      | g, T.Dot (T.Idx k, s'), I.Decl (g', T.UDec (I.BDec (l, (_, s)))) ->
          ignore (checkSub g s' g');
          let (T.UDec (I.BDec (l1, (_, s1)))) = T.ctxDec g k in
          begin if l <> l1 then raise (Error "Sub isn't well typed!")
          else
            begin if Conv.convSub (I.comp s (T.coerceSub s')) s1 then ()
            else raise (Error "Sub isn't well typed!")
            end
          end
      | g, T.Dot (T.Idx k, s), I.Decl (g', T.PDec (_, f', _, _)) ->
          ignore (checkSub g s g');
          let (T.PDec (_, f1, _, _)) = T.ctxDec g k in
          convFor (g, (f1, T.id), (f', s))
      | g, T.Dot (T.Exp m, s), I.Decl (g', T.UDec (I.Dec (_, a))) ->
          ignore (checkSub g s g');
          TypeCheck.typeCheck (T.coerceCtx g) (m, I.EClo (a, T.coerceSub s))
      | psi, T.Dot (T.Prg p, t), I.Decl (psi', T.PDec (_, f', _, _)) ->
          ignore (chatter 4 (function () -> "$"));
          ignore (checkSub psi t psi');
          ignore (isValue p);
          checkPrg psi (p, (f', t))
      | psi, T.Dot (T.Block b, t), I.Decl (psi', T.UDec (I.BDec (l2, (c, s2))))
        ->
          ignore (chatter 4 (function () -> "$"));
          ignore (checkSub psi t psi');
          let g, l = I.constBlock c in
          ignore (TypeCheck.typeCheckSub (T.coerceCtx psi') s2 g);
          checkBlock (psi, (b, (c, I.comp s2 (T.coerceSub t))))
      | psi, T.Dot _, I.Null -> raise (Error "Sub is not well typed")

    and checkBlock (psi, a) = match a with
      | (I.Bidx v, (c2, s2)) ->
          let (T.UDec (I.BDec (l1, (c1, s1)))) = T.ctxDec psi v in
          begin if c1 <> c2 then raise (Error "Sub isn't well typed!")
          else
            begin if Conv.convSub s2 s1 then ()
            else raise (Error "Sub isn't well typed!")
            end
          end
      | (I.Inst ul, (c2, s2)) ->
          let g, l = I.constBlock c2 in
          ignore (TypeCheck.typeCheckSub (T.coerceCtx psi) s2 g);
          checkInst (psi, ul, (1, l, s2))

    and checkInst (psi, a, b) = match a, b with
      | [], (_, [], _) -> ()
      | u :: ul, (n, d :: l, s2) ->
          let g = T.coerceCtx psi in
          let (I.Dec (_, v)) = I.decSub d s2 in
          ignore (TypeCheck.typeCheck g (u, v));
          checkInst (psi, ul, (n + 1, l, I.dot1 s2))

    and isValue = function
      | T.Var _ -> ()
      | T.PClo (T.Lam _, _) -> ()
      | T.PairExp (m, p) -> isValue p
      | T.PairBlock _ -> ()
      | T.PairPrg (p1, p2) -> begin
          isValue p1;
          isValue p2
        end
      | Unit -> ()
      | T.Rec _ -> ()
      | T.Const lemma ->
          begin match T.lemmaLookup lemma with
          | T.ForDec _ -> raise (Error "Lemma isn't a value")
          | T.ValDec (_, p, _) -> isValue p
          end
      | _ -> raise (Error "P isn't Value!")

    let check (psi, (p, f)) = checkPrg psi (p, (f, T.id))
  end

  (* no other cases can occur *)
  (*     inferCon (Psi, (H, t)) = (F', t')

       Invariant:
       If   Psi  |- t : Psi1
       and  Psi1 |- H : F
       then Psi  |- F'[t'] == F[t]
    
    fun inferCon (Psi, T.Const lemma) = inferLemma lemma
      | inferCon (Psi, T.Var k) =
          case T.ctxDec (Psi, k) of T.PDec (_, F') => F'
*)
  (* inferSpine (Psi, (S, t1), (F, t2)) = (F', t')

       Invariant:
       If   Psi  |- t1 : Psi1
       and  Psi1 |- S : F' > F''
       and  Psi  |- t2 : Psi2
       and  Psi2 |- F for
       and  Psi  |- F'[t1] == F[t2]
       then Psi  |- F''[t1] == F'[t']
    *)
  (* Blocks T.Inst, and T.LVar excluded for now *)
  (* checkPrg (Psi, P, F) = ()

       Invariant:
       If   Psi  |- t1 : Psi1
       and  Psi1 |- P : F'
       and  Psi  |- F for     (F in normal form)
       and  P does not contain any P closures
       then checkPrg returns () iff F'[t1] == F[id]
    *)
  (* Psi |- let xx :: F1 = P1 in P2 : F2' *)
  (* Psi |- t : Psi' *)
  (* Psi' |- F2 for *)
  (* Psi |- F2' = F2[t] *)
  (* Psi |- F1 :: for *)
  (* Psi |- P1 :: F1' *)
  (* Psi, D |- P2 :: (F2' [^]) *)
  (* Psi' |- F2' :: for *)
  (* Psi, D |- t o ^ :: Psi' *)
  (* Psi |- F1 == F1' for *)
  (* D'' == D *)
  (* don't forget to check if the worlds match up --cs Mon Apr 21 01:51:58 2003 *)
  (* checkCases (Psi, (Omega, (F, t2))) = ()
       Invariant:
       and  Psi |- Omega : F'
       and  Psi |- F' for
       then checkCases returns () iff Psi |- F' == F [t2] formula
    *)
  (* Psi' |- t' :: Psi *)
  (* convFor (Psi, (F1, t1), (F2, t2)) = ()

       Invariant:
       If   Psi |- t1 :: Psi1
       and  Ps1 |- F1 for
    *)
  (* also check that both worlds are equal -- cs Mon Apr 21 01:28:01 2003 *)
  (* For s1==s2, the variables in s1 and s2 must refer to the same cell in the context -- Yu Liao *)
  (* checkConv doesn't need context G?? -- Yu Liao *)
  (* checkSub (Psi, t, Psi') = ()

       Invariant
       If Psi |- t: Psi' then checkSub terminates with ()
       otherwise exception Error is raised
    *)
  (* Psi |- t : Psi' *)
  (* Psi' |- s2 : SOME variables of c *)
  (* Psi |- s2 : G *)
  (* Psi |- s2 : G *)
  (* Invariant:

      If   Psi |- s2 : Psi'    Psi' |-  Bn ... Bm
      and  Psi |- s : [cn :An ... cm:Am]
      and  Ai == Bi n<= i<=m
      then checkInst returns () otherwise an exception is raised.
   *)
  (*  remove later!
    and isValue (T.Lam _) = ()
      | isValue (T.PairExp (M, P)) = isValue P
      | isValue (T.PairBlock _ ) = ()
      | isValue (T.PairPrg (P1, P2)) = (isValue P1; isValue P2)
      | isValue T.Unit = ()
      | isValue (T.Root ((T.Const lemma), T.Nil)) =  could lemma be a VALUE? -- Yu Liao 
        ( case (T.lemmaLookup lemma) of
              T.ForDec _ => raise Error ""Lemma isn't a value""
            | T.ValDec(_,P,_) => isValue P )

      | isValue (T.Root ((T.Var k), T.Nil)) = ()
      | isValue (T.Rec _) = ()

       ABP 1/23/03 
      | isValue (T.EVar _) = raise Error ""It is an EVar""

      | isValue _ = raise Error ""P isn't Value!""
*)
  let checkPrg psi (p, f) = checkPrg psi (p, (f, T.id))
  let checkSub = checkSub
  let checkFor psi f = checkFor psi (f, T.id)
  let checkCtx = checkCtx
end

(* # 1 "src/tomega/TomegaTypecheck.sml.ml" *)
