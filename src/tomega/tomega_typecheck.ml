(* # 1 "src/tomega/tomega_typecheck.sig.ml" *)
open! Basis
module Tomega = Lambda_.Tomega

(* Type checking for functional proof term calculus *)
(* Author: Carsten Schuermann *)
(* Modified: Yu Liao *)
module type TOMEGATYPECHECK = sig
  exception Error of string

  val checkCtx : Tomega.dec IntSyn.ctx -> unit
  val checkFor : Tomega.dec IntSyn.ctx * Tomega.for_ -> unit
  val checkPrg : Tomega.dec IntSyn.ctx * (Tomega.prg * Tomega.for_) -> unit

  val checkSub :
    Tomega.dec IntSyn.ctx * Tomega.sub * Tomega.dec IntSyn.ctx -> unit
end
(* Signature TOMEGATYPECHECK *)

(* # 1 "src/tomega/tomega_typecheck.fun.ml" *)
open! Basis

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
  module Subordinate : SUBORDINATE
  module Weaken : WEAKEN
  module TomegaAbstract : Tomega_abstract.TOMEGAABSTRACT
end) : TOMEGATYPECHECK = struct
  (*! structure IntSyn = IntSyn' !*)
  (*! structure Tomega = Tomega' !*)
  exception Error of string

  open! struct
    module I = IntSyn
    module T = Tomega
    module S = Subordinate
    module TA = TomegaTypeCheck__0.TomegaAbstract

    let rec chatter chlev f =
      begin if !Global.chatter >= chlev then print (f ()) else ()
      end

    let rec normalizeHead = function
      | T.Const lemma, t -> T.Const lemma
      | T.Var k, t -> begin match T.varSub (k, t) with T.Idx k' -> T.Var k' end

    let rec inferSpine (psi_, s_, ft_) = inferSpineW (psi_, s_, T.whnfFor ft_)

    and inferSpineW = function
      | psi_, T.Nil, (f_, t) -> (f_, t)
      | psi_, T.AppExp (m_, s_), (T.All ((T.UDec (I.Dec (_, a_)), _), f_), t) ->
          let _ = chatter 4 (function () -> "[appExp") in
          let g_ = T.coerceCtx psi_ in
          let _ = TypeCheck.typeCheck (g_, (m_, I.EClo (a_, T.coerceSub t))) in
          let _ = chatter 4 (function () -> "]") in
          inferSpine (psi_, s_, (f_, T.Dot (T.Exp m_, t)))
      | ( psi_,
          T.AppBlock (I.Bidx k, s_),
          (T.All ((T.UDec (I.BDec (_, (cid, s))), _), f2_), t2) ) ->
          let (T.UDec (I.BDec (_, (cid', s')))) = T.ctxDec (psi_, k) in
          let g'_, _ = I.conDecBlock (I.sgnLookup cid') in
          let _ =
            begin if cid <> cid' then raise (Error "Block label incompatible")
            else ()
            end
          in
          let s'' = T.coerceSub (T.comp (T.embedSub s, t2)) in
          let _ = Conv.convSub (s', s'') in
          inferSpine (psi_, s_, (f2_, T.Dot (T.Block (I.Bidx k), t2)))
      | psi_, T.AppPrg (p_, s_), (T.All ((T.PDec (_, f1_, _, _), _), f2_), t) ->
          let _ = checkPrg (psi_, (p_, (f1_, t))) in
          inferSpine (psi_, s_, (f2_, T.dot1 t))
      | psi_, _, _ -> raise (Error "applied, but not of function type.")

    and inferPrg = function
      | psi_, T.Lam (d_, p_) ->
          let f_ = inferPrg (I.Decl (psi_, d_), p_) in
          T.All ((d_, T.Explicit), f_)
      | psi_, T.New p_ ->
          let (T.All ((T.UDec (I.BDec _ as d_), _), f_)) =
            inferPrg (psi_, p_)
          in
          TA.raiseF (I.Decl (I.Null, d_), (f_, I.id))
      | psi_, T.PairExp (u_, p_) ->
          let v_ = TypeCheck.infer' (T.coerceCtx psi_, u_) in
          let f_ = inferPrg (psi_, p_) in
          T.Ex ((I.Dec (None, v_), T.Explicit), f_)
      | psi_, T.PairBlock (I.Bidx k, p_) ->
          let d_ = I.ctxLookup (T.coerceCtx psi_, k) in
          let f_ = inferPrg (psi_, p_) in
          T.Ex ((d_, T.Explicit), f_)
      | psi_, T.PairPrg (p1_, p2_) ->
          let f1_ = inferPrg (psi_, p1_) in
          let f2_ = inferPrg (psi_, p2_) in
          T.And (f1_, f2_)
      | psi_, Unit -> T.True
      | psi_, T.Var k -> begin
          match T.ctxDec (psi_, k) with T.PDec (_, f'_, _, _) -> f'_
        end
      | psi_, T.Const c -> inferLemma c
      | psi_, T.Redex (p_, s_) ->
          let f1_ = inferPrg (psi_, p_) in
          let f2_ = inferSpine (psi_, s_, (f1_, T.id)) in
          T.forSub f2_
      | psi_, T.Rec ((T.PDec (_, f_, _, _) as d_), p_) ->
          let _ = checkPrg (I.Decl (psi_, d_), (p_, (f_, T.id))) in
          f_
      | psi_, T.Let ((T.PDec (_, f1_, _, _) as d_), p1_, p2_) ->
          let _ = checkPrg (psi_, (p1_, (f1_, T.id))) in
          let f2_ = inferPrg (I.Decl (psi_, d_), p2_) in
          f2_

    and checkPrg (psi_, (p_, ft_)) = checkPrgW (psi_, (p_, T.whnfFor ft_))

    and checkPrgW = function
      | _, (Unit, (True, _)) ->
          let _ = chatter 4 (function () -> "[true]") in
          ()
      | psi_, (T.Const lemma, (f_, t)) ->
          convFor (psi_, (inferLemma lemma, T.id), (f_, t))
      | psi_, (T.Var k, (f_, t)) -> begin
          match T.ctxDec (psi_, k) with
          | T.PDec (_, f'_, _, _) -> convFor (psi_, (f'_, T.id), (f_, t))
        end
      | ( psi_,
          ( T.Lam ((T.PDec (x, f1_, _, _) as d_), p_),
            (T.All ((T.PDec (x', f1'_, _, _), _), f2_), t) ) ) ->
          let _ = chatter 4 (function () -> "[lam[p]") in
          let _ = convFor (psi_, (f1_, T.id), (f1'_, t)) in
          let _ = chatter 4 (function () -> "]") in
          checkPrg (I.Decl (psi_, d_), (p_, (f2_, T.dot1 t)))
      | psi_, (T.Lam (T.UDec d_, p_), (T.All ((T.UDec d'_, _), f_), t2)) ->
          let _ = chatter 4 (function () -> "[lam[u]") in
          let _ = Conv.convDec ((d_, I.id), (d'_, T.coerceSub t2)) in
          let _ = chatter 4 (function () -> "]") in
          checkPrg (I.Decl (psi_, T.UDec d_), (p_, (f_, T.dot1 t2)))
      | psi_, (T.PairExp (m_, p_), (T.Ex ((I.Dec (x, a_), _), f2_), t)) ->
          let _ = chatter 4 (function () -> "[pair [e]") in
          let g_ = T.coerceCtx psi_ in
          let _ = TypeCheck.typeCheck (g_, (m_, I.EClo (a_, T.coerceSub t))) in
          let _ = chatter 4 (function () -> "]") in
          checkPrg (psi_, (p_, (f2_, T.Dot (T.Exp m_, t))))
      | ( psi_,
          ( T.PairBlock (I.Bidx k, p_),
            (T.Ex ((I.BDec (_, (cid, s)), _), f2_), t) ) ) ->
          let (T.UDec (I.BDec (_, (cid', s')))) = T.ctxDec (psi_, k) in
          let g'_, _ = I.conDecBlock (I.sgnLookup cid) in
          let _ =
            begin if cid' <> cid then raise (Error "Block label mismatch")
            else ()
            end
          in
          let _ =
            convSub
              (psi_, T.embedSub s', T.comp (T.embedSub s, t), T.revCoerceCtx g'_)
          in
          checkPrg (psi_, (p_, (f2_, T.Dot (T.Block (I.Bidx k), t))))
      | psi_, (T.PairPrg (p1_, p2_), (T.And (f1_, f2_), t)) ->
          let _ = chatter 4 (function () -> "[and") in
          let _ = checkPrg (psi_, (p1_, (f1_, t))) in
          let _ = chatter 4 (function () -> "...") in
          let _ = checkPrg (psi_, (p2_, (f2_, t))) in
          let _ = chatter 4 (function () -> "]") in
          ()
      | psi_, (T.Case omega_, ft_) -> checkCases (psi_, (omega_, ft_))
      | psi_, (T.Rec ((T.PDec (x, f_, _, _) as d_), p_), (f'_, t)) ->
          let _ = chatter 4 (function () -> "[rec") in
          let _ = convFor (psi_, (f_, T.id), (f'_, t)) in
          let _ = chatter 4 (function () -> "]\n") in
          checkPrg (I.Decl (psi_, d_), (p_, (f'_, t)))
      | psi_, (T.Let ((T.PDec (_, f1_, _, _) as d_), p1_, p2_), (f2_, t)) ->
          let _ = chatter 4 (function () -> "[let") in
          let _ = checkPrg (psi_, (p1_, (f1_, T.id))) in
          let _ = chatter 4 (function () -> ".") in
          let _ =
            checkPrg (I.Decl (psi_, d_), (p2_, (f2_, T.comp (t, T.shift))))
          in
          let _ = chatter 4 (function () -> "]\n") in
          ()
      | ( psi_,
          ( T.New (T.Lam (T.UDec (I.BDec (_, (cid, s)) as d_), p_) as p'_),
            (f_, t) ) ) ->
          let _ = chatter 5 (function () -> "[new1...") in
          let (T.All ((T.UDec d''_, _), f'_)) = inferPrg (psi_, p'_) in
          let _ = chatter 5 (function () -> "][new2...") in
          let f''_ = TA.raiseF (I.Decl (I.Null, d_), (f'_, I.id)) in
          begin
            convFor (psi_, (f''_, T.id), (f_, t));
            chatter 5 (function () -> "]\n")
          end
      | psi_, (T.Redex (p1_, s2_), (f_, t)) ->
          let f'_ = inferPrg (psi_, p1_) in
          checkSpine (psi_, s2_, (f'_, T.id), (f_, t))
      | psi_, (T.Box (w_, p_), (T.World (w'_, f_), t)) ->
          checkPrgW (psi_, (p_, (f_, t)))

    and checkSpine = function
      | psi_, T.Nil, (f_, t), (f'_, t') -> convFor (psi_, (f_, t), (f'_, t'))
      | ( psi_,
          T.AppExp (u_, s_),
          (T.All ((T.UDec (I.Dec (_, v_)), _), f_), t),
          (f'_, t') ) -> begin
          TypeCheck.typeCheck
            (T.coerceCtx psi_, (u_, I.EClo (v_, T.coerceSub t)));
          checkSpine (psi_, s_, (f_, T.Dot (T.Exp u_, t)), (f'_, t'))
        end
      | ( psi_,
          T.AppPrg (p_, s_),
          (T.All ((T.PDec (_, f1_, _, _), _), f2_), t),
          (f'_, t') ) -> begin
          checkPrgW (psi_, (p_, (f1_, t)));
          checkSpine (psi_, s_, (f2_, T.Dot (T.Undef, t)), (f'_, t'))
        end
      | psi_, T.AppExp (u_, s_), (T.FClo (f_, t1), t), (f'_, t') ->
          checkSpine (psi_, T.AppExp (u_, s_), (f_, T.comp (t1, t)), (f'_, t'))

    and checkCases = function
      | psi_, (T.Cases [], (f2_, t2)) -> ()
      | psi_, (T.Cases ((psi'_, t', p_) :: omega_), (f2_, t2)) ->
          let _ = chatter 4 (function () -> "[case... ") in
          let _ = chatter 4 (function () -> "sub... ") in
          let _ = checkSub (psi'_, t', psi_) in
          let _ = chatter 4 (function () -> "prg... ") in
          let t2' = T.comp (t2, t') in
          let _ = checkCtx psi_ in
          let _ = checkCtx psi'_ in
          let _ = chatter 4 (function () -> "]") in
          let _ = checkPrg (psi'_, (p_, (f2_, t2'))) in
          let _ = chatter 4 (function () -> "]\n") in
          let _ = checkCases (psi_, (T.Cases omega_, (f2_, t2))) in
          ()

    and inferLemma lemma =
      begin match T.lemmaLookup lemma with
      | T.ForDec (_, f_) -> f_
      | T.ValDec (_, _, f_) -> f_
      end

    and convFor (psi_, ft1_, ft2_) =
      convForW (psi_, T.whnfFor ft1_, T.whnfFor ft2_)

    and convForW = function
      | _, (T.True, _), (T.True, _) -> ()
      | ( psi_,
          (T.All (((T.UDec (I.Dec (_, a1_)) as d_), _), f1_), t1),
          (T.All ((T.UDec (I.Dec (_, a2_)), _), f2_), t2) ) ->
          let g_ = T.coerceCtx psi_ in
          let s1 = T.coerceSub t1 in
          let s2 = T.coerceSub t2 in
          let _ = Conv.conv ((a1_, s1), (a2_, s2)) in
          let _ = TypeCheck.typeCheck (g_, (I.EClo (a1_, s1), I.Uni I.Type)) in
          let _ = TypeCheck.typeCheck (g_, (I.EClo (a2_, s2), I.Uni I.Type)) in
          let d'_ = T.decSub (d_, t1) in
          let _ =
            convFor (I.Decl (psi_, d'_), (f1_, T.dot1 t1), (f2_, T.dot1 t2))
          in
          ()
      | ( psi_,
          (T.All (((T.UDec (I.BDec (_, (l1, s1))) as d_), _), f1_), t1),
          (T.All ((T.UDec (I.BDec (_, (l2, s2))), _), f2_), t2) ) ->
          let _ =
            begin if l1 <> l2 then raise (Error "Contextblock clash") else ()
            end
          in
          let g'_, _ = I.conDecBlock (I.sgnLookup l1) in
          let _ =
            convSub
              ( psi_,
                T.comp (T.embedSub s1, t1),
                T.comp (T.embedSub s2, t2),
                T.embedCtx g'_ )
          in
          let d'_ = T.decSub (d_, t1) in
          let _ =
            convFor (I.Decl (psi_, d'_), (f1_, T.dot1 t1), (f2_, T.dot1 t2))
          in
          ()
      | ( psi_,
          (T.Ex (((I.Dec (_, a1_) as d_), _), f1_), t1),
          (T.Ex ((I.Dec (_, a2_), _), f2_), t2) ) ->
          let g_ = T.coerceCtx psi_ in
          let s1 = T.coerceSub t1 in
          let s2 = T.coerceSub t2 in
          let _ = Conv.conv ((a1_, s1), (a2_, s2)) in
          let _ = TypeCheck.typeCheck (g_, (I.EClo (a1_, s1), I.Uni I.Type)) in
          let _ = TypeCheck.typeCheck (g_, (I.EClo (a2_, s2), I.Uni I.Type)) in
          let d'_ = I.decSub (d_, s1) in
          let _ =
            convFor
              (I.Decl (psi_, T.UDec d'_), (f1_, T.dot1 t1), (f2_, T.dot1 t2))
          in
          ()
      | ( psi_,
          (T.Ex (((I.BDec (name, (l1, s1)) as d_), _), f1_), t1),
          (T.Ex ((I.BDec (_, (l2, s2)), _), f2_), t2) ) ->
          let _ =
            begin if l1 <> l2 then raise (Error "Contextblock clash") else ()
            end
          in
          let g'_, _ = I.conDecBlock (I.sgnLookup l1) in
          let s1 = T.coerceSub t1 in
          let _ =
            convSub
              ( psi_,
                T.comp (T.embedSub s1, t1),
                T.comp (T.embedSub s2, t2),
                T.embedCtx g'_ )
          in
          let d'_ = I.decSub (d_, s1) in
          let _ =
            convFor
              (I.Decl (psi_, T.UDec d'_), (f1_, T.dot1 t1), (f2_, T.dot1 t2))
          in
          ()
      | psi_, (T.And (f1_, f1'_), t1), (T.And (f2_, f2'_), t2) ->
          let _ = convFor (psi_, (f1_, t1), (f2_, t2)) in
          let _ = convFor (psi_, (f1'_, t1), (f2'_, t2)) in
          ()
      | ( psi_,
          (T.All (((T.PDec (_, f1_, _, _) as d_), _), f1'_), t1),
          (T.All ((T.PDec (_, f2_, _, _), _), f2'_), t2) ) ->
          let _ = convFor (psi_, (f1_, t1), (f2_, t2)) in
          let d'_ = T.decSub (d_, t1) in
          let _ =
            convFor (I.Decl (psi_, d'_), (f1'_, T.dot1 t1), (f2'_, T.dot1 t2))
          in
          ()
      | psi_, (T.World (w1_, f1_), t1), (T.World (w2_, f2_), t2) ->
          let _ = convFor (psi_, (f1_, t1), (f2_, t2)) in
          ()
      | _ -> raise (Error "Typecheck error")

    and convSub = function
      | g_, T.Shift k1, T.Shift k2, g'_ -> begin
          if k1 = k2 then () else raise (Error "Sub not equivalent")
        end
      | g_, T.Shift k, (T.Dot _ as s2), g'_ ->
          convSub (g_, T.Dot (T.Idx (k + 1), T.Shift (k + 1)), s2, g'_)
      | g_, (T.Dot _ as s1), T.Shift k, g'_ ->
          convSub (g_, s1, T.Dot (T.Idx (k + 1), T.Shift (k + 1)), g'_)
      | g_, T.Dot (T.Idx k1, s1), T.Dot (T.Idx k2, s2), I.Decl (g'_, _) -> begin
          if k1 = k2 then convSub (g_, s1, s2, g'_)
          else raise (Error "Sub not equivalent")
        end
      | ( g_,
          T.Dot (T.Exp m1_, s1),
          T.Dot (T.Exp m2_, s2),
          I.Decl (g'_, T.UDec (I.Dec (_, a_))) ) ->
          let _ = TypeCheck.checkConv (m1_, m2_) in
          let _ = TypeCheck.typeCheck (T.coerceCtx g_, (m1_, a_)) in
          convSub (g_, s1, s2, g'_)
      | ( g_,
          T.Dot (T.Block (I.Bidx v1), s1),
          T.Dot (T.Block (I.Bidx v2), s2),
          I.Decl (g'_, T.UDec (I.BDec (_, (l, s)))) ) ->
          let (T.UDec (I.BDec (_, (l1, s11)))) = T.ctxDec (g_, v1) in
          let (T.UDec (I.BDec (_, (l2, s22)))) = T.ctxDec (g_, v2) in
          let _ =
            begin if l1 = l2 then () else raise (Error "Sub not equivalent")
            end
          in
          let _ =
            begin if l1 = l then () else raise (Error "Sub not equivalent")
            end
          in
          let g''_, _ = I.conDecBlock (I.sgnLookup l) in
          let _ =
            convSub (g_, T.embedSub s11, T.embedSub s22, T.revCoerceCtx g''_)
          in
          let _ =
            convSub (g_, T.embedSub s11, T.embedSub s, T.revCoerceCtx g''_)
          in
          convSub (g_, s1, s2, g'_)
      | ( g_,
          T.Dot (T.Prg p1_, s1),
          T.Dot (T.Prg p2_, s2),
          I.Decl (g'_, T.PDec (_, f_, _, _)) ) ->
          let _ = isValue p1_ in
          let _ = isValue p2_ in
          let _ = convValue (g_, p1_, p2_, f_) in
          convSub (g_, s1, s2, g'_)
      | ( g_,
          T.Dot (T.Idx k1, s1),
          T.Dot (T.Exp m2_, s2),
          I.Decl (g'_, T.UDec (I.Dec (_, a_))) ) ->
          let _ = TypeCheck.checkConv (I.Root (I.BVar k1, I.Nil), m2_) in
          let _ = TypeCheck.typeCheck (T.coerceCtx g_, (m2_, a_)) in
          convSub (g_, s1, s2, g'_)
      | ( g_,
          T.Dot (T.Exp m1_, s1),
          T.Dot (T.Idx k2, s2),
          I.Decl (g'_, T.UDec (I.Dec (_, a_))) ) ->
          let _ = TypeCheck.checkConv (m1_, I.Root (I.BVar k2, I.Nil)) in
          let _ = TypeCheck.typeCheck (T.coerceCtx g_, (m1_, a_)) in
          convSub (g_, s1, s2, g'_)
      | ( g_,
          T.Dot (T.Idx k1, s1),
          T.Dot (T.Prg p2_, s2),
          I.Decl (g'_, T.PDec (_, f_, _, _)) ) ->
          let _ = isValue p2_ in
          let _ = convValue (g_, T.Var k1, p2_, f_) in
          convSub (g_, s1, s2, g'_)
      | ( g_,
          T.Dot (T.Prg p1_, s1),
          T.Dot (T.Idx k2, s2),
          I.Decl (g'_, T.PDec (_, f_, _, _)) ) ->
          let _ = isValue p1_ in
          let _ = convValue (g_, p1_, T.Var k2, f_) in
          convSub (g_, s1, s2, g'_)

    and convValue (g_, p1_, p2_, f_) = ()

    and checkFor = function
      | psi_, (True, _) -> ()
      | psi_, (T.All (((T.PDec (_, f1_, _, _) as d_), _), f2_), t) -> begin
          checkFor (psi_, (f1_, t));
          checkFor (I.Decl (psi_, d_), (f2_, T.dot1 t))
        end
      | psi_, (T.All (((T.UDec d_ as d'_), _), f_), t) -> begin
          TypeCheck.checkDec (T.coerceCtx psi_, (d_, T.coerceSub t));
          checkFor (I.Decl (psi_, d'_), (f_, T.dot1 t))
        end
      | psi_, (T.Ex ((d_, _), f_), t) -> begin
          TypeCheck.checkDec (T.coerceCtx psi_, (d_, T.coerceSub t));
          checkFor (I.Decl (psi_, T.UDec d_), (f_, T.dot1 t))
        end
      | psi_, (T.And (f1_, f2_), t) -> begin
          checkFor (psi_, (f1_, t));
          checkFor (psi_, (f2_, t))
        end
      | psi_, (T.FClo (f_, t'), t) -> checkFor (psi_, (f_, T.comp (t', t)))
      | psi_, (T.World (w_, f_), t) -> checkFor (psi_, (f_, t))

    and checkCtx = function
      | I.Null -> ()
      | I.Decl (psi_, T.UDec d_) -> begin
          checkCtx psi_;
          TypeCheck.checkDec (T.coerceCtx psi_, (d_, I.id))
        end
      | I.Decl (psi_, T.PDec (_, f_, _, _)) -> begin
          checkCtx psi_;
          checkFor (psi_, (f_, T.id))
        end

    and checkSub = function
      | I.Null, T.Shift 0, I.Null -> ()
      | I.Decl (g_, d_), T.Shift k, I.Null -> begin
          if k > 0 then checkSub (g_, T.Shift (k - 1), I.Null)
          else raise (Error "Sub is not well typed!")
        end
      | g_, T.Shift k, g'_ ->
          checkSub (g_, T.Dot (T.Idx (k + 1), T.Shift (k + 1)), g'_)
      | g_, T.Dot (T.Idx k, s'), I.Decl (g'_, T.UDec (I.Dec (_, a_))) ->
          let _ = checkSub (g_, s', g'_) in
          let (T.UDec (I.Dec (_, a'_))) = T.ctxDec (g_, k) in
          begin if Conv.conv ((a'_, I.id), (a_, T.coerceSub s')) then ()
          else raise (Error "Sub isn't well typed!")
          end
      | g_, T.Dot (T.Idx k, s'), I.Decl (g'_, T.UDec (I.BDec (l, (_, s)))) ->
          let _ = checkSub (g_, s', g'_) in
          let (T.UDec (I.BDec (l1, (_, s1)))) = T.ctxDec (g_, k) in
          begin if l <> l1 then raise (Error "Sub isn't well typed!")
          else begin
            if Conv.convSub (I.comp (s, T.coerceSub s'), s1) then ()
            else raise (Error "Sub isn't well typed!")
          end
          end
      | g_, T.Dot (T.Idx k, s), I.Decl (g'_, T.PDec (_, f'_, _, _)) ->
          let _ = checkSub (g_, s, g'_) in
          let (T.PDec (_, f1_, _, _)) = T.ctxDec (g_, k) in
          convFor (g_, (f1_, T.id), (f'_, s))
      | g_, T.Dot (T.Exp m_, s), I.Decl (g'_, T.UDec (I.Dec (_, a_))) ->
          let _ = checkSub (g_, s, g'_) in
          TypeCheck.typeCheck (T.coerceCtx g_, (m_, I.EClo (a_, T.coerceSub s)))
      | psi_, T.Dot (T.Prg p_, t), I.Decl (psi'_, T.PDec (_, f'_, _, _)) ->
          let _ = chatter 4 (function () -> "$") in
          let _ = checkSub (psi_, t, psi'_) in
          let _ = isValue p_ in
          checkPrg (psi_, (p_, (f'_, t)))
      | ( psi_,
          T.Dot (T.Block b_, t),
          I.Decl (psi'_, T.UDec (I.BDec (l2, (c, s2)))) ) ->
          let _ = chatter 4 (function () -> "$") in
          let _ = checkSub (psi_, t, psi'_) in
          let g_, l_ = I.constBlock c in
          let _ = TypeCheck.typeCheckSub (T.coerceCtx psi'_, s2, g_) in
          checkBlock (psi_, (b_, (c, I.comp (s2, T.coerceSub t))))
      | psi_, T.Dot _, I.Null -> raise (Error "Sub is not well typed")

    and checkBlock = function
      | psi_, (I.Bidx v, (c2, s2)) ->
          let (T.UDec (I.BDec (l1, (c1, s1)))) = T.ctxDec (psi_, v) in
          begin if c1 <> c2 then raise (Error "Sub isn't well typed!")
          else begin
            if Conv.convSub (s2, s1) then ()
            else raise (Error "Sub isn't well typed!")
          end
          end
      | psi_, (I.Inst ul_, (c2, s2)) ->
          let g_, l_ = I.constBlock c2 in
          let _ = TypeCheck.typeCheckSub (T.coerceCtx psi_, s2, g_) in
          checkInst (psi_, ul_, (1, l_, s2))

    and checkInst = function
      | psi_, [], (_, [], _) -> ()
      | psi_, u_ :: ul_, (n, d_ :: l_, s2) ->
          let g_ = T.coerceCtx psi_ in
          let (I.Dec (_, v_)) = I.decSub (d_, s2) in
          let _ = TypeCheck.typeCheck (g_, (u_, v_)) in
          checkInst (psi_, ul_, (n + 1, l_, I.dot1 s2))

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
      | T.Const lemma -> begin
          match T.lemmaLookup lemma with
          | T.ForDec _ -> raise (Error "Lemma isn't a value")
          | T.ValDec (_, p_, _) -> isValue p_
        end
      | _ -> raise (Error "P isn't Value!")

    let rec check (psi_, (p_, f_)) = checkPrg (psi_, (p_, (f_, T.id)))
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
  let checkPrg (psi_, (p_, f_)) = checkPrg (psi_, (p_, (f_, T.id)))
  let checkSub = checkSub
  let checkFor (psi_, f_) = checkFor (psi_, (f_, T.id))
  let checkCtx = checkCtx
end

(* # 1 "src/tomega/tomega_typecheck.sml.ml" *)
