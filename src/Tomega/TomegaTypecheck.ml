open! Basis
open! Global
open! Global.Global_
open! Intsyn
open! Intsyn.Lambda_
open! Worldcheck
open! Worldcheck.Worldcheck_
open! Cover
open! Cover.Cover_
open! Formatter
open! Formatter__Formatter_
open! Names
open! Names.Names_
open! Print
open! Print.Print_
open! Typecheck
open! Typecheck.Typecheck_
open! Subordinate
open! Subordinate
open! Meta
open! Meta.Meta_
open! Modes
open! Modes.Modes_
open! Trail
open! Trail.Trail_

(* # 1 "src/tomega/TomegaTypecheck.sig.ml" *)
open! Basis
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

    let rec inferSpine (psi, s_, (f_, t_)) = inferSpineW (psi, s_, T.whnfFor f_ t_)

    and inferSpineW (psi, a, b) = match a, b with
      | T.Nil, (f_, t) -> (f_, t)
      | T.AppExp (m_, s_), (T.All ((T.UDec (I.Dec (_, a_)), _), f_), t) ->
          ignore (chatter 4 (function () -> "[appExp"));
          let g_ = T.coerceCtx psi in
          ignore (TypeCheck.typeCheck g_ (m_, I.EClo (a_, T.coerceSub t)));
          ignore (chatter 4 (function () -> "]"));
          inferSpine (psi, s_, (f_, T.Dot (T.Exp m_, t)))
      | T.AppBlock (I.Bidx k, s_), (T.All ((T.UDec (I.BDec (_, (cid, s))), _), f2_), t2) ->
          let (T.UDec (I.BDec (_, (cid', s')))) = T.ctxDec psi k in
          let g'_, _ = I.conDecBlock (I.sgnLookup cid') in
          ignore begin if cid <> cid' then raise (Error "Block label incompatible")
            else ()
            end;
          let s'' = T.coerceSub (T.comp (T.embedSub s) t2) in
          ignore (Conv.convSub s' s'');
          inferSpine (psi, s_, (f2_, T.Dot (T.Block (I.Bidx k), t2)))
      | T.AppPrg (p_, s_), (T.All ((T.PDec (_, f1_, _, _), _), f2_), t) ->
          ignore (checkPrg psi (p_, (f1_, t)));
          inferSpine (psi, s_, (f2_, T.dot1 t))
      | _, _ -> raise (Error "applied, but not of function type.")

    and inferPrg (psi, a) = match a with
      | T.Lam (d_, p_) ->
          let f_ = inferPrg (I.Decl (psi, d_), p_) in
          T.All ((d_, T.Explicit), f_)
      | T.New p_ ->
          let (T.All ((T.UDec (I.BDec _ as d_), _), f_)) = inferPrg (psi, p_) in
          TA.raiseF (I.Decl (I.Null, d_)) (f_, I.id)
      | T.PairExp (u_, p_) ->
          let v_ = TypeCheck.infer' (T.coerceCtx psi) u_ in
          let f_ = inferPrg (psi, p_) in
          T.Ex ((I.Dec (None, v_), T.Explicit), f_)
      | T.PairBlock (I.Bidx k, p_) ->
          let d_ = I.ctxLookup (T.coerceCtx psi) k in
          let f_ = inferPrg (psi, p_) in
          T.Ex ((d_, T.Explicit), f_)
      | T.PairPrg (p1_, p2_) ->
          let f1_ = inferPrg (psi, p1_) in
          let f2_ = inferPrg (psi, p2_) in
          T.And (f1_, f2_)
      | Unit -> T.True
      | T.Var k ->
          begin match T.ctxDec psi k with T.PDec (_, f'_, _, _) -> f'_
          end
      | T.Const c -> inferLemma c
      | T.Redex (p_, s_) ->
          let f1_ = inferPrg (psi, p_) in
          let f2_ = inferSpine (psi, s_, (f1_, T.id)) in
          (let f__, t__ = f2_ in T.forSub f__ t__)
      | T.Rec ((T.PDec (_, f_, _, _) as d_), p_) ->
          ignore (checkPrg (I.Decl (psi, d_)) (p_, (f_, T.id)));
          f_
      | T.Let ((T.PDec (_, f1_, _, _) as d_), p1_, p2_) ->
          ignore (checkPrg psi (p1_, (f1_, T.id)));
          let f2_ = inferPrg (I.Decl (psi, d_), p2_) in
          f2_

    and checkPrg psi (p_, (f_, t_)) = checkPrgW (psi, (p_, T.whnfFor f_ t_))

    and checkPrgW = function
      | _, (Unit, (True, _)) ->
          ignore (chatter 4 (function () -> "[true]"));
          ()
      | psi, (T.Const lemma, (f_, t)) ->
          convFor (psi, (inferLemma lemma, T.id), (f_, t))
      | psi, (T.Var k, (f_, t)) ->
          begin match T.ctxDec psi k with
          | T.PDec (_, f'_, _, _) -> convFor (psi, (f'_, T.id), (f_, t))
          end
      | ( psi,
          ( T.Lam ((T.PDec (x, f1_, _, _) as d_), p_),
            (T.All ((T.PDec (x', f1', _, _), _), f2_), t) ) ) ->
          ignore (chatter 4 (function () -> "[lam[p]"));
          ignore (convFor (psi, (f1_, T.id), (f1', t)));
          ignore (chatter 4 (function () -> "]"));
          checkPrg (I.Decl (psi, d_)) (p_, (f2_, T.dot1 t))
      | psi, (T.Lam (T.UDec d_, p_), (T.All ((T.UDec d'_, _), f_), t2)) ->
          ignore (chatter 4 (function () -> "[lam[u]"));
          ignore (Conv.convDec (d_, I.id) (d'_, T.coerceSub t2));
          ignore (chatter 4 (function () -> "]"));
          checkPrg (I.Decl (psi, T.UDec d_)) (p_, (f_, T.dot1 t2))
      | psi, (T.PairExp (m_, p_), (T.Ex ((I.Dec (x, a_), _), f2_), t)) ->
          ignore (chatter 4 (function () -> "[pair [e]"));
          let g_ = T.coerceCtx psi in
          ignore (TypeCheck.typeCheck g_ (m_, I.EClo (a_, T.coerceSub t)));
          ignore (chatter 4 (function () -> "]"));
          checkPrg psi (p_, (f2_, T.Dot (T.Exp m_, t)))
      | ( psi,
          ( T.PairBlock (I.Bidx k, p_),
            (T.Ex ((I.BDec (_, (cid, s)), _), f2_), t) ) ) ->
          let (T.UDec (I.BDec (_, (cid', s')))) = T.ctxDec psi k in
          let g'_, _ = I.conDecBlock (I.sgnLookup cid) in
          ignore begin if cid' <> cid then raise (Error "Block label mismatch")
            else ()
            end;
          ignore (convSub
              (psi, T.embedSub s', T.comp (T.embedSub s) t, T.revCoerceCtx g'_));
          checkPrg psi (p_, (f2_, T.Dot (T.Block (I.Bidx k), t)))
      | psi, (T.PairPrg (p1_, p2_), (T.And (f1_, f2_), t)) ->
          ignore (chatter 4 (function () -> "[and"));
          ignore (checkPrg psi (p1_, (f1_, t)));
          ignore (chatter 4 (function () -> "..."));
          ignore (checkPrg psi (p2_, (f2_, t)));
          ignore (chatter 4 (function () -> "]"));
          ()
      | psi, (T.Case omega_, ft_) -> checkCases (psi, (omega_, ft_))
      | psi, (T.Rec ((T.PDec (x, f_, _, _) as d_), p_), (f'_, t)) ->
          ignore (chatter 4 (function () -> "[rec"));
          ignore (convFor (psi, (f_, T.id), (f'_, t)));
          ignore (chatter 4 (function () -> "]\n"));
          checkPrg (I.Decl (psi, d_)) (p_, (f'_, t))
      | psi, (T.Let ((T.PDec (_, f1_, _, _) as d_), p1_, p2_), (f2_, t)) ->
          ignore (chatter 4 (function () -> "[let"));
          ignore (checkPrg psi (p1_, (f1_, T.id)));
          ignore (chatter 4 (function () -> "."));
          ignore (checkPrg (I.Decl (psi, d_)) (p2_, (f2_, T.comp t T.shift)));
          ignore (chatter 4 (function () -> "]\n"));
          ()
      | ( psi,
          ( T.New (T.Lam (T.UDec (I.BDec (_, (cid, s)) as d_), p_) as p'_),
            (f_, t) ) ) ->
          ignore (chatter 5 (function () -> "[new1..."));
          let (T.All ((T.UDec d''_, _), f'_)) = inferPrg (psi, p'_) in
          ignore (chatter 5 (function () -> "][new2..."));
          let f''_ = TA.raiseF (I.Decl (I.Null, d_)) (f'_, I.id) in
          convFor (psi, (f''_, T.id), (f_, t));
          chatter 5 (function () -> "]\n")
      | psi, (T.Redex (p1_, s2_), (f_, t)) ->
          let f'_ = inferPrg (psi, p1_) in
          checkSpine (psi, s2_, (f'_, T.id), (f_, t))
      | psi, (T.Box (w_, p_), (T.World (w'_, f_), t)) ->
          checkPrgW (psi, (p_, (f_, t)))

    and checkSpine (psi, a, b, c) = match a, b, c with
      | T.Nil, (f_, t), (f'_, t') -> convFor (psi, (f_, t), (f'_, t'))
      | T.AppExp (u_, s_), (T.All ((T.UDec (I.Dec (_, v_)), _), f_), t), (f'_, t') -> begin
          TypeCheck.typeCheck (T.coerceCtx psi) (u_, I.EClo (v_, T.coerceSub t));
          checkSpine (psi, s_, (f_, T.Dot (T.Exp u_, t)), (f'_, t'))
        end
      | T.AppPrg (p_, s_), (T.All ((T.PDec (_, f1_, _, _), _), f2_), t), (f'_, t') -> begin
          checkPrgW (psi, (p_, (f1_, t)));
          checkSpine (psi, s_, (f2_, T.Dot (T.Undef, t)), (f'_, t'))
        end
      | T.AppExp (u_, s_), (T.FClo (f_, t1), t), (f'_, t') ->
          checkSpine (psi, T.AppExp (u_, s_), (f_, T.comp t1 t), (f'_, t'))

    and checkCases (psi, a) = match a with
      | (T.Cases [], (f2_, t2)) -> ()
      | (T.Cases ((psi', t', p_) :: omega_), (f2_, t2)) ->
          ignore (chatter 4 (function () -> "[case... "));
          ignore (chatter 4 (function () -> "sub... "));
          ignore (checkSub psi' t' psi);
          ignore (chatter 4 (function () -> "prg... "));
          let t2' = T.comp t2 t' in
          ignore (checkCtx psi);
          ignore (checkCtx psi');
          ignore (chatter 4 (function () -> "]"));
          ignore (checkPrg psi' (p_, (f2_, t2')));
          ignore (chatter 4 (function () -> "]\n"));
          ignore (checkCases (psi, (T.Cases omega_, (f2_, t2))));
          ()

    and inferLemma lemma =
      begin match T.lemmaLookup lemma with
      | T.ForDec (_, f_) -> f_
      | T.ValDec (_, _, f_) -> f_
      end

    and convFor (psi, (f1_, t1_), (f2_, t2_)) = convForW (psi, T.whnfFor f1_ t1_, T.whnfFor f2_ t2_)

    and convForW = function
      | _, (T.True, _), (T.True, _) -> ()
      | ( psi,
          (T.All (((T.UDec (I.Dec (_, a1_)) as d_), _), f1_), t1),
          (T.All ((T.UDec (I.Dec (_, a2_)), _), f2_), t2) ) ->
          let g_ = T.coerceCtx psi in
          let s1 = T.coerceSub t1 in
          let s2 = T.coerceSub t2 in
          ignore (Conv.conv (a1_, s1) (a2_, s2));
          ignore (TypeCheck.typeCheck g_ (I.EClo (a1_, s1), I.Uni I.Type));
          ignore (TypeCheck.typeCheck g_ (I.EClo (a2_, s2), I.Uni I.Type));
          let d'_ = T.decSub d_ t1 in
          ignore (convFor (I.Decl (psi, d'_), (f1_, T.dot1 t1), (f2_, T.dot1 t2)));
          ()
      | ( psi,
          (T.All (((T.UDec (I.BDec (_, (l1, s1))) as d_), _), f1_), t1),
          (T.All ((T.UDec (I.BDec (_, (l2, s2))), _), f2_), t2) ) ->
          ignore begin if l1 <> l2 then raise (Error "Contextblock clash") else ()
            end;
          let g'_, _ = I.conDecBlock (I.sgnLookup l1) in
          ignore (convSub
              ( psi,
                T.comp (T.embedSub s1) t1,
                T.comp (T.embedSub s2) t2,
                T.embedCtx g'_ ));
          let d'_ = T.decSub d_ t1 in
          ignore (convFor (I.Decl (psi, d'_), (f1_, T.dot1 t1), (f2_, T.dot1 t2)));
          ()
      | ( psi,
          (T.Ex (((I.Dec (_, a1_) as d_), _), f1_), t1),
          (T.Ex ((I.Dec (_, a2_), _), f2_), t2) ) ->
          let g_ = T.coerceCtx psi in
          let s1 = T.coerceSub t1 in
          let s2 = T.coerceSub t2 in
          ignore (Conv.conv (a1_, s1) (a2_, s2));
          ignore (TypeCheck.typeCheck g_ (I.EClo (a1_, s1), I.Uni I.Type));
          ignore (TypeCheck.typeCheck g_ (I.EClo (a2_, s2), I.Uni I.Type));
          let d'_ = I.decSub d_ s1 in
          ignore (convFor
              (I.Decl (psi, T.UDec d'_), (f1_, T.dot1 t1), (f2_, T.dot1 t2)));
          ()
      | ( psi,
          (T.Ex (((I.BDec (name, (l1, s1)) as d_), _), f1_), t1),
          (T.Ex ((I.BDec (_, (l2, s2)), _), f2_), t2) ) ->
          ignore begin if l1 <> l2 then raise (Error "Contextblock clash") else ()
            end;
          let g'_, _ = I.conDecBlock (I.sgnLookup l1) in
          let s1 = T.coerceSub t1 in
          ignore (convSub
              ( psi,
                T.comp (T.embedSub s1) t1,
                T.comp (T.embedSub s2) t2,
                T.embedCtx g'_ ));
          let d'_ = I.decSub d_ s1 in
          ignore (convFor
              (I.Decl (psi, T.UDec d'_), (f1_, T.dot1 t1), (f2_, T.dot1 t2)));
          ()
      | psi, (T.And (f1_, f1'), t1), (T.And (f2_, f2'), t2) ->
          ignore (convFor (psi, (f1_, t1), (f2_, t2)));
          ignore (convFor (psi, (f1', t1), (f2', t2)));
          ()
      | ( psi,
          (T.All (((T.PDec (_, f1_, _, _) as d_), _), f1'), t1),
          (T.All ((T.PDec (_, f2_, _, _), _), f2'), t2) ) ->
          ignore (convFor (psi, (f1_, t1), (f2_, t2)));
          let d'_ = T.decSub d_ t1 in
          ignore (convFor (I.Decl (psi, d'_), (f1', T.dot1 t1), (f2', T.dot1 t2)));
          ()
      | psi, (T.World (w1_, f1_), t1), (T.World (w2_, f2_), t2) ->
          ignore (convFor (psi, (f1_, t1), (f2_, t2)));
          ()
      | _ -> raise (Error "Typecheck error")

    and convSub (g_, a, b, c) = match a, b, c with
      | T.Shift k1, T.Shift k2, g'_ ->
          begin if k1 = k2 then () else raise (Error "Sub not equivalent")
          end
      | T.Shift k, (T.Dot _ as s2), g'_ ->
          convSub (g_, T.Dot (T.Idx (k + 1), T.Shift (k + 1)), s2, g'_)
      | (T.Dot _ as s1), T.Shift k, g'_ ->
          convSub (g_, s1, T.Dot (T.Idx (k + 1), T.Shift (k + 1)), g'_)
      | T.Dot (T.Idx k1, s1), T.Dot (T.Idx k2, s2), I.Decl (g'_, _) ->
          begin if k1 = k2 then convSub (g_, s1, s2, g'_)
          else raise (Error "Sub not equivalent")
          end
      | T.Dot (T.Exp m1_, s1), T.Dot (T.Exp m2_, s2), I.Decl (g'_, T.UDec (I.Dec (_, a_))) ->
          ignore (TypeCheck.checkConv m1_ m2_);
          ignore (TypeCheck.typeCheck (T.coerceCtx g_) (m1_, a_));
          convSub (g_, s1, s2, g'_)
      | T.Dot (T.Block (I.Bidx v1), s1), T.Dot (T.Block (I.Bidx v2), s2), I.Decl (g'_, T.UDec (I.BDec (_, (l, s)))) ->
          let (T.UDec (I.BDec (_, (l1, s11)))) = T.ctxDec g_ v1 in
          let (T.UDec (I.BDec (_, (l2, s22)))) = T.ctxDec g_ v2 in
          ignore begin if l1 = l2 then () else raise (Error "Sub not equivalent")
            end;
          ignore begin if l1 = l then () else raise (Error "Sub not equivalent")
            end;
          let g''_, _ = I.conDecBlock (I.sgnLookup l) in
          ignore (convSub (g_, T.embedSub s11, T.embedSub s22, T.revCoerceCtx g''_));
          ignore (convSub (g_, T.embedSub s11, T.embedSub s, T.revCoerceCtx g''_));
          convSub (g_, s1, s2, g'_)
      | T.Dot (T.Prg p1_, s1), T.Dot (T.Prg p2_, s2), I.Decl (g'_, T.PDec (_, f_, _, _)) ->
          ignore (isValue p1_);
          ignore (isValue p2_);
          ignore (convValue (g_, p1_, p2_, f_));
          convSub (g_, s1, s2, g'_)
      | T.Dot (T.Idx k1, s1), T.Dot (T.Exp m2_, s2), I.Decl (g'_, T.UDec (I.Dec (_, a_))) ->
          ignore (TypeCheck.checkConv (I.Root (I.BVar k1, I.Nil)) m2_);
          ignore (TypeCheck.typeCheck (T.coerceCtx g_) (m2_, a_));
          convSub (g_, s1, s2, g'_)
      | T.Dot (T.Exp m1_, s1), T.Dot (T.Idx k2, s2), I.Decl (g'_, T.UDec (I.Dec (_, a_))) ->
          ignore (TypeCheck.checkConv m1_ (I.Root (I.BVar k2, I.Nil)));
          ignore (TypeCheck.typeCheck (T.coerceCtx g_) (m1_, a_));
          convSub (g_, s1, s2, g'_)
      | T.Dot (T.Idx k1, s1), T.Dot (T.Prg p2_, s2), I.Decl (g'_, T.PDec (_, f_, _, _)) ->
          ignore (isValue p2_);
          ignore (convValue (g_, T.Var k1, p2_, f_));
          convSub (g_, s1, s2, g'_)
      | T.Dot (T.Prg p1_, s1), T.Dot (T.Idx k2, s2), I.Decl (g'_, T.PDec (_, f_, _, _)) ->
          ignore (isValue p1_);
          ignore (convValue (g_, p1_, T.Var k2, f_));
          convSub (g_, s1, s2, g'_)

    and convValue (g_, p1_, p2_, f_) = ()

    and checkFor a1 b1 = match a1, b1 with
      | psi, (T.True, _) -> ()
      | psi, (T.All (((T.PDec (_, f1_, _, _) as d_), _), f2_), t) -> begin
          checkFor psi (f1_, t);
          checkFor (I.Decl (psi, d_)) (f2_, T.dot1 t)
        end
      | psi, (T.All (((T.UDec d_ as d'_), _), f_), t) -> begin
          TypeCheck.checkDec (T.coerceCtx psi) (d_, T.coerceSub t);
          checkFor (I.Decl (psi, d'_)) (f_, T.dot1 t)
        end
      | psi, (T.Ex ((d_, _), f_), t) -> begin
          TypeCheck.checkDec (T.coerceCtx psi) (d_, T.coerceSub t);
          checkFor (I.Decl (psi, T.UDec d_)) (f_, T.dot1 t)
        end
      | psi, (T.And (f1_, f2_), t) -> begin
          checkFor psi (f1_, t);
          checkFor psi (f2_, t)
        end
      | psi, (T.FClo (f_, t'), t) -> checkFor psi (f_, T.comp t' t)
      | psi, (T.World (w_, f_), t) -> checkFor psi (f_, t)

    and checkCtx = function
      | I.Null -> ()
      | I.Decl (psi, T.UDec d_) -> begin
          checkCtx psi;
          TypeCheck.checkDec (T.coerceCtx psi) (d_, I.id)
        end
      | I.Decl (psi, T.PDec (_, f_, _, _)) -> begin
          checkCtx psi;
          checkFor psi (f_, T.id)
        end

    and checkSub a3 b3 c3 = match a3, b3, c3 with
      | I.Null, T.Shift 0, I.Null -> ()
      | I.Decl (g_, d_), T.Shift k, I.Null ->
          begin if k > 0 then checkSub g_ (T.Shift (k - 1)) I.Null
          else raise (Error "Sub is not well typed!")
          end
      | g_, T.Shift k, g'_ ->
          checkSub g_ (T.Dot (T.Idx (k + 1), T.Shift (k + 1))) g'_
      | g_, T.Dot (T.Idx k, s'), I.Decl (g'_, T.UDec (I.Dec (_, a_))) ->
          ignore (checkSub g_ s' g'_);
          let (T.UDec (I.Dec (_, a'_))) = T.ctxDec g_ k in
          begin if Conv.conv (a'_, I.id) (a_, T.coerceSub s') then ()
          else raise (Error "Sub isn't well typed!")
          end
      | g_, T.Dot (T.Idx k, s'), I.Decl (g'_, T.UDec (I.BDec (l, (_, s)))) ->
          ignore (checkSub g_ s' g'_);
          let (T.UDec (I.BDec (l1, (_, s1)))) = T.ctxDec g_ k in
          begin if l <> l1 then raise (Error "Sub isn't well typed!")
          else
            begin if Conv.convSub (I.comp s (T.coerceSub s')) s1 then ()
            else raise (Error "Sub isn't well typed!")
            end
          end
      | g_, T.Dot (T.Idx k, s), I.Decl (g'_, T.PDec (_, f'_, _, _)) ->
          ignore (checkSub g_ s g'_);
          let (T.PDec (_, f1_, _, _)) = T.ctxDec g_ k in
          convFor (g_, (f1_, T.id), (f'_, s))
      | g_, T.Dot (T.Exp m_, s), I.Decl (g'_, T.UDec (I.Dec (_, a_))) ->
          ignore (checkSub g_ s g'_);
          TypeCheck.typeCheck (T.coerceCtx g_) (m_, I.EClo (a_, T.coerceSub s))
      | psi, T.Dot (T.Prg p_, t), I.Decl (psi', T.PDec (_, f'_, _, _)) ->
          ignore (chatter 4 (function () -> "$"));
          ignore (checkSub psi t psi');
          ignore (isValue p_);
          checkPrg psi (p_, (f'_, t))
      | psi, T.Dot (T.Block b_, t), I.Decl (psi', T.UDec (I.BDec (l2, (c, s2))))
        ->
          ignore (chatter 4 (function () -> "$"));
          ignore (checkSub psi t psi');
          let g_, l_ = I.constBlock c in
          ignore (TypeCheck.typeCheckSub (T.coerceCtx psi') s2 g_);
          checkBlock (psi, (b_, (c, I.comp s2 (T.coerceSub t))))
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
      | (I.Inst ul_, (c2, s2)) ->
          let g_, l_ = I.constBlock c2 in
          ignore (TypeCheck.typeCheckSub (T.coerceCtx psi) s2 g_);
          checkInst (psi, ul_, (1, l_, s2))

    and checkInst (psi, a, b) = match a, b with
      | [], (_, [], _) -> ()
      | u_ :: ul_, (n, d_ :: l_, s2) ->
          let g_ = T.coerceCtx psi in
          let (I.Dec (_, v_)) = I.decSub d_ s2 in
          ignore (TypeCheck.typeCheck g_ (u_, v_));
          checkInst (psi, ul_, (n + 1, l_, I.dot1 s2))

    and isValue = function
      | T.Var _ -> ()
      | T.PClo (T.Lam _, _) -> ()
      | T.PairExp (m_, p_) -> isValue p_
      | T.PairBlock _ -> ()
      | T.PairPrg (p1_, p2_) -> begin
          isValue p1_;
          isValue p2_
        end
      | Unit -> ()
      | T.Rec _ -> ()
      | T.Const lemma ->
          begin match T.lemmaLookup lemma with
          | T.ForDec _ -> raise (Error "Lemma isn't a value")
          | T.ValDec (_, p_, _) -> isValue p_
          end
      | _ -> raise (Error "P isn't Value!")

    let check (psi, (p_, f_)) = checkPrg psi (p_, (f_, T.id))
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
  let checkPrg psi (p_, f_) = checkPrg psi (p_, (f_, T.id))
  let checkSub = checkSub
  let checkFor psi f_ = checkFor psi (f_, T.id)
  let checkCtx = checkCtx
end

(* # 1 "src/tomega/TomegaTypecheck.sml.ml" *)
