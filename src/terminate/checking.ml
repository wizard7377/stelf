(* # 1 "src/terminate/checking.sig.ml" *)
open! Basis

(* Reasoning about orders *)
(* Author: Brigitte Pientka *)
module type CHECKING = sig
  (*! structure IntSyn : INTSYN !*)
  module Order : ORDER

  (*! structure Paths : PATHS !*)
  (* If Q marks all parameters in a context G we write   G : Q  *)
  type quantifier_ = All | Exist | And of Paths.occ

  (* Quantifier to mark parameters *)
  (* Q ::= All                     *)
  (*     | Exist                     *)
  (*     | And                     *)
  type 'a predicate_ =
    | Less of 'a * 'a
    | Leq of 'a * 'a
    | Eq of 'a * 'a
    | Pi of IntSyn.dec_ * 'a predicate_

  type nonrec order = (IntSyn.eclo * IntSyn.eclo) Order.order_

  (* reduction predicate context (unordered) *)
  type nonrec rctx = order predicate_ list

  (* mixed-prefix context *)
  type nonrec qctx = quantifier_ IntSyn.ctx_

  val shiftRCtx : rctx -> (IntSyn.sub_ -> IntSyn.sub_) -> rctx

  val shiftPred :
    order predicate_ -> (IntSyn.sub_ -> IntSyn.sub_) -> order predicate_

  val deduce : IntSyn.dctx * qctx * rctx * order predicate_ -> bool
end
(* signature CHECKING *)

(* # 1 "src/terminate/checking.fun.ml" *)
open! Basis

(* Reasoning about structural orders *)
(* Author: Brigitte Pientka *)
(* for reasoning about orders see [Pientka IJCAR'01] *)
module Checking (Checking__0 : sig
  module Global : GLOBAL

  (*! structure IntSyn' : INTSYN !*)
  module Whnf : WHNF

  (*! sharing Whnf.IntSyn = IntSyn' !*)
  module Conv : CONV

  (*! sharing Conv.IntSyn = IntSyn' !*)
  module Unify : UNIFY

  (*! sharing Unify.IntSyn = IntSyn' !*)
  module Names : NAMES

  (*! sharing Names.IntSyn = IntSyn' !*)
  module Index : INDEX

  (*! sharing Index.IntSyn = IntSyn' !*)
  module Subordinate : SUBORDINATE

  (*! sharing Subordinate.IntSyn = IntSyn' !*)
  module Formatter : FORMATTER
  module Print : PRINT

  (*! sharing Print.IntSyn = IntSyn' !*)
  module Order : ORDER

  (*! sharing Order.IntSyn = IntSyn' !*)
  (*! structure Paths  : PATHS !*)
  module Origins : Origins.ORIGINS
end) : CHECKING = struct
  (*! structure IntSyn = IntSyn' !*)
  module Order = Order

  (*! structure Paths = Paths !*)
  type quantifier_ = All | Exist | And of Paths.occ

  (* Quantifier to mark parameters *)
  (* Q ::= All                     *)
  (*     | Exist                   *)
  (*     | And                     *)
  (* If Q marks all parameters in a context G we write   G : Q               *)
  type 'a predicate_ =
    | Less of 'a * 'a
    | Leq of 'a * 'a
    | Eq of 'a * 'a
    | Pi of IntSyn.dec_ * 'a predicate_

  (* Abbreviation *)
  type nonrec order = (IntSyn.eclo * IntSyn.eclo) Order.order_

  (* reduction order assumptions (unordered) *)
  type nonrec rctx = order predicate_ list

  (* mixed prefix order contex *)
  type nonrec qctx = quantifier_ IntSyn.ctx_

  open! struct
    module I = IntSyn
    module P = Paths
    module N = Names
    module F = Print.Formatter
    module R = Order
    module Unify = Checking__0.Unify

    let mkEClo (u, s) = I.EClo (u, s)

    let rec atomicPredToString = function
      | g_, Less ((us_, _), (us'_, _)) ->
          (Print.expToString (g_, mkEClo us_) ^ " < ")
          ^ Print.expToString (g_, mkEClo us'_)
      | g_, Leq ((us_, _), (us'_, _)) ->
          (Print.expToString (g_, mkEClo us_) ^ " <= ")
          ^ Print.expToString (g_, mkEClo us'_)
      | g_, Eq ((us_, _), (us'_, _)) ->
          (Print.expToString (g_, mkEClo us_) ^ " = ")
          ^ Print.expToString (g_, mkEClo us'_)

    let rec atomicRCtxToString = function
      | g_, [] -> " "
      | g_, o_ :: [] -> atomicPredToString (g_, o_)
      | g_, o_ :: d'_ ->
          (atomicRCtxToString (g_, d'_) ^ ", ") ^ atomicPredToString (g_, o_)

    let rec shiftO arg__1 arg__2 =
      begin match (arg__1, arg__2) with
      | R.Arg ((u_, us), (v_, vs)), f -> R.Arg ((u_, f us), (v_, f vs))
      | R.Lex l_, f -> R.Lex (map (function o_ -> shiftO o_ f) l_)
      | R.Simul l_, f -> R.Simul (map (function o_ -> shiftO o_ f) l_)
      end

    let rec shiftP arg__3 arg__4 =
      begin match (arg__3, arg__4) with
      | Less (o1_, o2_), f -> Less (shiftO o1_ f, shiftO o2_ f)
      | Leq (o1_, o2_), f -> Leq (shiftO o1_ f, shiftO o2_ f)
      | Eq (o1_, o2_), f -> Eq (shiftO o1_ f, shiftO o2_ f)
      | Pi ((I.Dec (x_, v_) as d_), p_), f -> Pi (d_, shiftP p_ f)
      end

    let rec shiftRCtx rl_ f = map (function p -> shiftP p f) rl_

    let rec shiftArg arg__5 arg__6 =
      begin match (arg__5, arg__6) with
      | Less (((u1_, s1), (v1_, s1')), ((u2_, s2), (v2_, s2'))), f ->
          Less (((u1_, f s1), (v1_, f s1')), ((u2_, f s2), (v2_, f s2')))
      | Leq (((u1_, s1), (v1_, s1')), ((u2_, s2), (v2_, s2'))), f ->
          Leq (((u1_, f s1), (v1_, f s1')), ((u2_, f s2), (v2_, f s2')))
      | Eq (((u1_, s1), (v1_, s1')), ((u2_, s2), (v2_, s2'))), f ->
          Eq (((u1_, f s1), (v1_, f s1')), ((u2_, f s2), (v2_, f s2')))
      end

    let rec shiftACtx rl_ f = map (function p -> shiftArg p f) rl_

    let rec fmtOrder (g_, o_) =
      let rec fmtOrder' = function
        | R.Arg (((u_, s) as us_), ((v_, s') as vs_)) ->
            F.hbox
              [ F.string "("; Print.formatExp (g_, mkEClo us_); F.string ")" ]
        | R.Lex l_ ->
            F.hbox
              [ F.string "{"; F.hOVbox0 1 0 1 (fmtOrders l_); F.string "}" ]
        | R.Simul l_ ->
            F.hbox
              [ F.string "["; F.hOVbox0 1 0 1 (fmtOrders l_); F.string "]" ]
      and fmtOrders = function
        | [] -> []
        | o_ :: [] -> [ fmtOrder' o_ ]
        | o_ :: l_ -> fmtOrder' o_ :: F.break :: fmtOrders l_
      in
      fmtOrder' o_

    let rec fmtComparison (g_, o_, comp, o'_) =
      F.hOVbox0 1 0 1
        [
          fmtOrder (g_, o_); F.break; F.string comp; F.break; fmtOrder (g_, o'_);
        ]

    let rec fmtPredicate' = function
      | g_, Less (o_, o'_) -> fmtComparison (g_, o_, "<", o'_)
      | g_, Leq (o_, o'_) -> fmtComparison (g_, o_, "<=", o'_)
      | g_, Eq (o_, o'_) -> fmtComparison (g_, o_, "=", o'_)
      | g_, Pi (d_, p_) ->
          F.hbox [ F.string "Pi "; fmtPredicate' (I.Decl (g_, d_), p_) ]

    let rec fmtPredicate (g_, p_) = fmtPredicate' (Names.ctxName g_, p_)

    let rec fmtRGCtx' = function
      | g_, [] -> ""
      | g_, p_ :: [] -> F.makestring_fmt (fmtPredicate' (g_, p_))
      | g_, p_ :: rl_ ->
          (F.makestring_fmt (fmtPredicate' (g_, p_)) ^ " ,")
          ^ fmtRGCtx' (g_, rl_)

    let rec fmtRGCtx (g_, rl_) = fmtRGCtx' (Names.ctxName g_, rl_)
    let rec init () = true
    let rec eqCid (c, c') = c = c'

    let rec conv ((us_, vs_), (us'_, vs'_)) =
      Conv.conv (vs_, vs'_) && Conv.conv (us_, us'_)

    let rec isUniversal = function
      | All -> true
      | Exist -> false
      | exist'_ -> false

    let rec isExistential = function
      | All -> false
      | Exist -> true
      | exist'_ -> true

    let rec isParameter (q_, x_) = isParameterW (q_, Whnf.whnf (x_, I.id))

    and isParameterW (q_, us_) =
      try isUniversal (I.ctxLookup (q_, Whnf.etaContract (mkEClo us_)))
      with eta_ -> isFreeEVar us_

    and isFreeEVar = function
      | I.EVar (_, _, _, { contents = [] }), _ -> true
      | I.Lam (d_, u_), s -> isFreeEVar (Whnf.whnf (u_, I.dot1 s))
      | _ -> false

    let rec isAtomic (gq_, us_) = isAtomicW (gq_, Whnf.whnf us_)

    and isAtomicW = function
      | gq_, ((I.Root (I.Const c, s_) as x_), s) -> isAtomicS (gq_, (s_, s))
      | gq_, ((I.Root (I.Def c, s_) as x_), s) -> isAtomicS (gq_, (s_, s))
      | ((g_, q_) as gq_), ((I.Root (I.BVar n, s_) as x_), s) ->
          isExistential (I.ctxLookup (q_, n)) || isAtomicS (gq_, (s_, s))
      | gq_, _ -> false

    and isAtomicS = function
      | gq_, (nil_, _) -> true
      | gq_, (I.SClo (s_, s'), s'') -> isAtomicS (gq_, (s_, I.comp (s', s'')))
      | gq_, (I.App (u'_, s'_), s1') -> false

    let rec eq (g_, (us_, vs_), (us'_, vs'_)) =
      Unify.unifiable (g_, vs_, vs'_) && Unify.unifiable (g_, us_, us'_)

    let rec lookupEq = function
      | gq_, [], usVs_, usVs'_, sc -> false
      | gq_, Less (_, _) :: d_, usVs_, usVs'_, sc ->
          lookupEq (gq_, d_, usVs_, usVs'_, sc)
      | ((g_, q_) as gq_), Eq (usVs1_, usVs1'_) :: d_, usVs_, usVs'_, sc ->
          Cs_manager.trail (function () ->
              eq (g_, usVs1_, usVs_) && eq (g_, usVs1'_, usVs'_) && sc ())
          || Cs_manager.trail (function () ->
              eq (g_, usVs1_, usVs'_) && eq (g_, usVs1'_, usVs_) && sc ())
          || lookupEq (gq_, d_, usVs_, usVs'_, sc)

    let rec lookupLt = function
      | gq_, [], usVs_, usVs'_, sc -> false
      | gq_, Eq (_, _) :: d_, usVs_, usVs'_, sc ->
          lookupLt (gq_, d_, usVs_, usVs'_, sc)
      | ((g_, q_) as gq_), Less (usVs1_, usVs1'_) :: d_, usVs_, usVs'_, sc ->
          Cs_manager.trail (function () ->
              eq (g_, usVs1_, usVs_) && eq (g_, usVs1'_, usVs'_) && sc ())
          || lookupLt (gq_, d_, usVs_, usVs'_, sc)

    let rec eqAtomic = function
      | ((g_, q_) as gq_), [], d'_, usVs_, usVs'_, sc ->
          Cs_manager.trail (function () -> eq (g_, usVs_, usVs'_) && sc ())
          || lookupEq (gq_, d'_, usVs_, usVs'_, sc)
      | ((g_, q_) as gq_), d_, d'_, usVs_, usVs'_, sc ->
          Cs_manager.trail (function () -> eq (g_, usVs_, usVs'_) && sc ())
          || lookupEq (gq_, d_, usVs_, usVs'_, sc)
          || lookupEq (gq_, d'_, usVs_, usVs'_, sc)
          || transEq (gq_, d_, d'_, usVs_, usVs'_, sc)

    and transEq = function
      | ((g_, q_) as gq_), [], d_, usVs_, usVs'_, sc -> false
      | ((g_, q_) as gq_), Eq (usVs1_, usVs1'_) :: d_, d'_, usVs_, usVs'_, sc ->
          Cs_manager.trail (function () ->
              eq (g_, usVs1'_, usVs'_)
              && sc ()
              && eqAtomicR (gq_, d_ @ d'_, usVs_, usVs1_, sc, atomic))
          || Cs_manager.trail (function () ->
              eq (g_, usVs1_, usVs'_)
              && sc ()
              && eqAtomicR (gq_, d_ @ d'_, usVs_, usVs1'_, sc, atomic))
          || transEq (gq_, d_, Eq (usVs1_, usVs1'_) :: d'_, usVs_, usVs'_, sc)
      | ((g_, q_) as gq_), Less (usVs1_, usVs1'_) :: d_, d'_, usVs_, usVs'_, sc
        ->
          transEq (gq_, d_, d'_, usVs_, usVs'_, sc)

    and ltAtomic = function
      | ((g_, q_) as gq_), [], d'_, usVs_, usVs'_, sc ->
          lookupLt (gq_, d'_, usVs_, usVs'_, sc)
      | ((g_, q_) as gq_), d_, d'_, usVs_, usVs'_, sc ->
          lookupLt (gq_, d_, usVs_, usVs'_, sc)
          || lookupLt (gq_, d'_, usVs_, usVs'_, sc)
          || transLt (gq_, d_, d'_, usVs_, usVs'_, sc)

    and transLt = function
      | ((g_, q_) as gq_), [], d_, usVs_, usVs'_, sc -> false
      | ((g_, q_) as gq_), Eq (usVs1_, usVs1'_) :: d_, d'_, usVs_, usVs'_, sc ->
          Cs_manager.trail (function () ->
              eq (g_, usVs1'_, usVs'_)
              && sc ()
              && ltAtomicR (gq_, d_ @ d'_, usVs_, usVs1_, sc, atomic))
          || Cs_manager.trail (function () ->
              eq (g_, usVs1_, usVs'_)
              && sc ()
              && ltAtomicR (gq_, d_ @ d'_, usVs_, usVs1'_, sc, atomic))
          || transLt (gq_, d_, Eq (usVs1_, usVs1'_) :: d'_, usVs_, usVs'_, sc)
      | ((g_, q_) as gq_), Less (usVs1_, usVs1'_) :: d_, d'_, usVs_, usVs'_, sc
        ->
          Cs_manager.trail (function () ->
              eq (g_, usVs1'_, usVs'_)
              && sc ()
              && eqAtomicR (gq_, d_ @ d'_, usVs_, usVs1_, sc, atomic))
          || Cs_manager.trail (function () ->
              eq (g_, usVs1'_, usVs'_)
              && sc ()
              && ltAtomicR (gq_, d_ @ d'_, usVs_, usVs1_, sc, atomic))
          || transLt (gq_, d_, Less (usVs1_, usVs1'_) :: d'_, usVs_, usVs'_, sc)

    and atomic = function
      | gq_, d_, d'_, Eq (usVs_, usVs'_), sc ->
          eqAtomic (gq_, d_, d'_, usVs_, usVs'_, sc)
      | gq_, d_, d'_, Less (usVs_, usVs'_), sc ->
          ltAtomic (gq_, d_, d'_, usVs_, usVs'_, sc)

    and leftInstantiate = function
      | ((g_, q_) as gq_), [], d'_, p_, sc -> begin
          if atomic (gq_, d'_, [], p_, sc) then begin
            begin if !Global.chatter > 4 then
              print
                ((((" Proved: " ^ atomicRCtxToString (g_, d'_)) ^ " ---> ")
                 ^ atomicPredToString (g_, p_))
                ^ "\n")
            else ()
            end;
            true
          end
          else false
        end
      | gq_, Less (usVs_, usVs'_) :: d_, d'_, p_, sc ->
          ltInstL (gq_, d_, d'_, usVs_, usVs'_, p_, sc)
      | gq_, Leq (usVs_, usVs'_) :: d_, d'_, p_, sc ->
          leInstL (gq_, d_, d'_, usVs_, usVs'_, p_, sc)
      | gq_, Eq (usVs_, usVs'_) :: d_, d'_, p_, sc ->
          eqInstL (gq_, d_, d'_, usVs_, usVs'_, p_, sc)

    and ltInstL (gq_, d_, d'_, usVs_, usVs'_, p'_, sc) =
      ltInstLW (gq_, d_, d'_, Whnf.whnfEta usVs_, usVs'_, p'_, sc)

    and ltInstLW = function
      | ( ((g_, q_) as gq_),
          d_,
          d'_,
          ( (I.Lam ((I.Dec (_, v1_) as dec_), u_), s1),
            (I.Pi ((I.Dec (_, v2_), _), v_), s2) ),
          ((u'_, s1'), (v'_, s2')),
          p'_,
          sc ) -> begin
          if Subordinate.equiv (I.targetFam v'_, I.targetFam v1_) then
            let x_ = I.newEVar (g_, I.EClo (v1_, s1)) in
            let sc' = function () -> isParameter (q_, x_) && sc () in
            ltInstL
              ( (g_, q_),
                d_,
                d'_,
                ((u_, I.Dot (I.Exp x_, s1)), (v_, I.Dot (I.Exp x_, s2))),
                ((u'_, s1'), (v'_, s2')),
                p'_,
                sc' )
          else begin
            if Subordinate.below (I.targetFam v1_, I.targetFam v'_) then
              let x_ = I.newEVar (g_, I.EClo (v1_, s1)) in
              ltInstL
                ( (g_, q_),
                  d_,
                  d'_,
                  ((u_, I.Dot (I.Exp x_, s1)), (v_, I.Dot (I.Exp x_, s2))),
                  ((u'_, s1'), (v'_, s2')),
                  p'_,
                  sc )
            else false
          end
        end
      | gq_, d_, d'_, usVs_, usVs'_, p'_, sc ->
          leftInstantiate (gq_, d_, Less (usVs_, usVs'_) :: d'_, p'_, sc)

    and leInstL (gq_, d_, d'_, usVs_, usVs'_, p'_, sc) =
      leInstLW (gq_, d_, d'_, Whnf.whnfEta usVs_, usVs'_, p'_, sc)

    and leInstLW = function
      | ( ((g_, q_) as gq_),
          d_,
          d'_,
          ( (I.Lam (I.Dec (_, v1_), u_), s1),
            (I.Pi ((I.Dec (_, v2_), _), v_), s2) ),
          ((u'_, s1'), (v'_, s2')),
          p'_,
          sc ) -> begin
          if Subordinate.equiv (I.targetFam v'_, I.targetFam v1_) then
            let x_ = I.newEVar (g_, I.EClo (v1_, s1)) in
            let sc' = function () -> isParameter (q_, x_) && sc () in
            leInstL
              ( (g_, q_),
                d_,
                d'_,
                ((u_, I.Dot (I.Exp x_, s1)), (v_, I.Dot (I.Exp x_, s2))),
                ((u'_, s1'), (v'_, s2')),
                p'_,
                sc' )
          else begin
            if Subordinate.below (I.targetFam v1_, I.targetFam v'_) then
              let x_ = I.newEVar (g_, I.EClo (v1_, s1)) in
              leInstL
                ( (g_, q_),
                  d_,
                  d'_,
                  ((u_, I.Dot (I.Exp x_, s1)), (v_, I.Dot (I.Exp x_, s2))),
                  ((u'_, s1'), (v'_, s2')),
                  p'_,
                  sc )
            else false
          end
        end
      | gq_, d_, d'_, usVs_, usVs'_, p_, sc ->
          leftInstantiate (gq_, d_, Less (usVs_, usVs'_) :: d'_, p_, sc)

    and eqInstL (gq_, d_, d'_, usVs_, usVs'_, p'_, sc) =
      eqInstLW (gq_, d_, d'_, Whnf.whnfEta usVs_, Whnf.whnfEta usVs'_, p'_, sc)

    and eqInstLW = function
      | ( ((g_, q_) as gq_),
          d_,
          d'_,
          ( (I.Lam (I.Dec (_, v1'_), u'_), s1'),
            (I.Pi ((I.Dec (_, v2'_), _), v'_), s2') ),
          ( (I.Lam (I.Dec (_, v1''_), u''_), s1''),
            (I.Pi ((I.Dec (_, v2''_), _), v''_), s2'') ),
          p'_,
          sc ) ->
          let x_ = I.newEVar (g_, I.EClo (v1''_, s1'')) in
          eqInstL
            ( gq_,
              d_,
              d'_,
              ((u'_, I.Dot (I.Exp x_, s1')), (v'_, I.Dot (I.Exp x_, s2'))),
              ((u''_, I.Dot (I.Exp x_, s1'')), (v''_, I.Dot (I.Exp x_, s2''))),
              p'_,
              function
              | () -> begin
                  ignore (isParameter (q_, x_));
                  sc ()
                end )
      | gq_, d_, d'_, usVs_, usVs'_, p'_, sc ->
          eqIL (gq_, d_, d'_, usVs_, usVs'_, p'_, sc)

    and eqIL = function
      | ( ((g_, q_) as gq_),
          d_,
          d'_,
          (((I.Root (I.Const c, s_), s), vs_) as usVs_),
          (((I.Root (I.Const c', s'_), s'), vs'_) as usVs'_),
          p'_,
          sc ) -> begin
          if eqCid (c, c') then
            eqSpineIL
              ( gq_,
                d_,
                d'_,
                ((s_, s), (I.constType c, I.id)),
                ((s'_, s'), (I.constType c', I.id)),
                p'_,
                sc )
          else begin
            begin if !Global.chatter > 4 then
              print
                (((((" Proved: "
                    ^ atomicRCtxToString (g_, Eq (usVs_, usVs'_) :: d_))
                   ^ atomicRCtxToString (g_, d'_))
                  ^ " ---> ")
                 ^ atomicPredToString (g_, p'_))
                ^ "\n")
            else ()
            end;
            true
          end
        end
      | ( ((g_, q_) as gq_),
          d_,
          d'_,
          (((I.Root (I.Def c, s_), s), vs_) as usVs_),
          (((I.Root (I.Def c', s'_), s'), vs'_) as usVs'_),
          p'_,
          sc ) -> begin
          if eqCid (c, c') then
            eqSpineIL
              ( gq_,
                d_,
                d'_,
                ((s_, s), (I.constType c, I.id)),
                ((s'_, s'), (I.constType c', I.id)),
                p'_,
                sc )
          else begin
            begin if !Global.chatter > 4 then
              print
                (((((" Proved: "
                    ^ atomicRCtxToString (g_, Eq (usVs_, usVs'_) :: d_))
                   ^ atomicRCtxToString (g_, d'_))
                  ^ " ---> ")
                 ^ atomicPredToString (g_, p'_))
                ^ "\n")
            else ()
            end;
            true
          end
        end
      | ( ((g_, q_) as gq_),
          d_,
          d'_,
          (((I.Root (I.Const c, s_), s) as us_), vs_),
          (((I.Root (I.BVar n, s'_), s') as us'_), vs'_),
          p'_,
          sc ) -> begin
          if isAtomic (gq_, us'_) then
            leftInstantiate
              (gq_, d_, Eq ((us'_, vs'_), (us_, vs_)) :: d'_, p'_, sc)
          else begin
            begin if !Global.chatter > 4 then
              print
                (((((" Proved: "
                    ^ atomicRCtxToString
                        (g_, Eq ((us_, vs_), (us'_, vs'_)) :: d_))
                   ^ atomicRCtxToString (g_, d'_))
                  ^ " ---> ")
                 ^ atomicPredToString (g_, p'_))
                ^ "\n")
            else ()
            end;
            true
          end
        end
      | ( ((g_, q_) as gq_),
          d_,
          d'_,
          (((I.Root (I.Def c, s_), s) as us_), vs_),
          (((I.Root (I.BVar n, s'_), s') as us'_), vs'_),
          p'_,
          sc ) -> begin
          if isAtomic (gq_, us'_) then
            leftInstantiate
              (gq_, d_, Eq ((us'_, vs'_), (us_, vs_)) :: d'_, p'_, sc)
          else begin
            begin if !Global.chatter > 4 then
              print
                (((((" Proved: "
                    ^ atomicRCtxToString
                        (g_, Eq ((us_, vs_), (us'_, vs'_)) :: d_))
                   ^ atomicRCtxToString (g_, d'_))
                  ^ " ---> ")
                 ^ atomicPredToString (g_, p'_))
                ^ "\n")
            else ()
            end;
            true
          end
        end
      | ( ((g_, q_) as gq_),
          d_,
          d'_,
          (((I.Root (I.BVar n, s_), s) as us_), vs_),
          (((I.Root (I.Def c, s'_), s') as us'_), vs'_),
          p'_,
          sc ) -> begin
          if isAtomic (gq_, us_) then
            leftInstantiate
              (gq_, d_, Eq ((us_, vs_), (us'_, vs'_)) :: d'_, p'_, sc)
          else begin
            begin if !Global.chatter > 4 then
              print
                (((((" Proved: "
                    ^ atomicRCtxToString
                        (g_, Eq ((us_, vs_), (us'_, vs'_)) :: d'_))
                   ^ atomicRCtxToString (g_, d'_))
                  ^ " ---> ")
                 ^ atomicPredToString (g_, p'_))
                ^ "\n")
            else ()
            end;
            true
          end
        end
      | ( ((g_, q_) as gq_),
          d_,
          d'_,
          (((I.Root (I.BVar n, s_), s) as us_), vs_),
          (((I.Root (I.Const c, s'_), s') as us'_), vs'_),
          p'_,
          sc ) -> begin
          if isAtomic (gq_, us_) then
            leftInstantiate
              (gq_, d_, Eq ((us_, vs_), (us'_, vs'_)) :: d'_, p'_, sc)
          else begin
            begin if !Global.chatter > 4 then
              print
                (((((" Proved: "
                    ^ atomicRCtxToString
                        (g_, Eq ((us_, vs_), (us'_, vs'_)) :: d'_))
                   ^ atomicRCtxToString (g_, d'_))
                  ^ " ---> ")
                 ^ atomicPredToString (g_, p'_))
                ^ "\n")
            else ()
            end;
            true
          end
        end
      | ( ((g_, q_) as gq_),
          d_,
          d'_,
          (((I.Root (I.BVar n, s_), s) as us_), vs_),
          (((I.Root (I.BVar n', s'_), s') as us'_), vs'_),
          p'_,
          sc ) -> begin
          if n = n' then
            let (I.Dec (_, v'_)) = I.ctxDec (g_, n) in
            eqSpineIL
              ( gq_,
                d_,
                d'_,
                ((s_, s), (v'_, I.id)),
                ((s'_, s'), (v'_, I.id)),
                p'_,
                sc )
          else
            leftInstantiate
              (gq_, d_, Eq ((us_, vs_), (us'_, vs'_)) :: d'_, p'_, sc)
        end
      | ((g_, q_) as gq_), d_, d'_, usVs_, usVs'_, p'_, sc -> begin
          begin if !Global.chatter > 4 then
            print
              (((((" Proved: "
                  ^ atomicRCtxToString (g_, Eq (usVs_, usVs'_) :: d_))
                 ^ atomicRCtxToString (g_, d'_))
                ^ " ---> ")
               ^ atomicPredToString (g_, p'_))
              ^ "\n")
          else ()
          end;
          true
        end

    and eqSpineIL (gq_, d_, d'_, (ss_, vs_), (ss'_, vs'_), p'_, sc) =
      eqSpineILW
        (gq_, d_, d'_, (ss_, Whnf.whnf vs_), (ss'_, Whnf.whnf vs'_), p'_, sc)

    and eqSpineILW = function
      | gq_, d_, d'_, ((Nil, s), vs_), ((Nil, s'), vs'_), p'_, sc ->
          leftInstantiate (gq_, d_, d'_, p'_, sc)
      | gq_, d_, d'_, ((I.SClo (s_, s'), s''), vs_), ssVs'_, p'_, sc ->
          eqSpineIL
            (gq_, d_, d'_, ((s_, I.comp (s', s'')), vs_), ssVs'_, p'_, sc)
      | gq_, d_, d'_, ssVs_, ((I.SClo (s'_, s'), s''), vs'_), p'_, sc ->
          eqSpineIL
            (gq_, d_, d'_, ssVs_, ((s'_, I.comp (s', s'')), vs'_), p'_, sc)
      | ( gq_,
          d_,
          d'_,
          ((I.App (u_, s_), s1), (I.Pi ((I.Dec (_, v1_), _), v2_), s2)),
          ((I.App (u'_, s'_), s1'), (I.Pi ((I.Dec (_, v1'_), _), v2'_), s2')),
          p'_,
          sc ) ->
          let d1_ =
            Eq (((u_, s1), (v1_, s2)), ((u'_, s1'), (v1'_, s2'))) :: d_
          in
          eqSpineIL
            ( gq_,
              d1_,
              d'_,
              ((s_, s1), (v2_, I.Dot (I.Exp (I.EClo (u_, s1)), s2))),
              ((s'_, s1'), (v2'_, I.Dot (I.Exp (I.EClo (u'_, s1')), s2'))),
              p'_,
              sc )

    and rightDecompose = function
      | gq_, d'_, Less (o_, o'_) -> ordLtR (gq_, d'_, o_, o'_)
      | gq_, d'_, Leq (o_, o'_) -> ordLeR (gq_, d'_, o_, o'_)
      | gq_, d'_, Eq (o_, o'_) -> ordEqR (gq_, d'_, o_, o'_)

    and ordLtR = function
      | gq_, d'_, R.Arg usVs_, R.Arg usVs'_ ->
          ltAtomicR (gq_, d'_, usVs_, usVs'_, init, leftInstantiate)
      | gq_, d'_, R.Lex o_, R.Lex o'_ -> ltLexR (gq_, d'_, o_, o'_)
      | gq_, d'_, R.Simul o_, R.Simul o'_ -> ltSimulR (gq_, d'_, o_, o'_)

    and ordLeR = function
      | gq_, d'_, R.Arg usVs_, R.Arg usVs'_ ->
          leAtomicR (gq_, d'_, usVs_, usVs'_, init, leftInstantiate)
      | gq_, d'_, R.Lex o_, R.Lex o'_ ->
          ltLexR (gq_, d'_, o_, o'_) || ordEqsR (gq_, d'_, o_, o'_)
      | gq_, d'_, R.Simul o_, R.Simul o'_ -> leSimulR (gq_, d'_, o_, o'_)

    and ordEqR = function
      | gq_, d'_, R.Arg usVs_, R.Arg usVs'_ ->
          conv (usVs_, usVs'_)
          || eqAtomicR (gq_, d'_, usVs_, usVs'_, init, leftInstantiate)
      | gq_, d'_, R.Lex o_, R.Lex o'_ -> ordEqsR (gq_, d'_, o_, o'_)
      | gq_, d'_, R.Simul o_, R.Simul o'_ -> ordEqsR (gq_, d'_, o_, o'_)

    and ordEqsR = function
      | gq_, d'_, [], [] -> true
      | gq_, d'_, o_ :: l_, o'_ :: l'_ ->
          ordEqR (gq_, d'_, o_, o'_) && ordEqsR (gq_, d'_, l_, l'_)

    and ltLexR = function
      | gq_, d'_, [], [] -> false
      | gq_, d'_, o_ :: l_, o'_ :: l'_ ->
          ordLtR (gq_, d'_, o_, o'_)
          || (ordEqR (gq_, d'_, o_, o'_) && ltLexR (gq_, d'_, l_, l'_))

    and leLexR (gq_, d'_, l_, l'_) =
      ltLexR (gq_, d'_, l_, l'_) || ordEqsR (gq_, d'_, l_, l'_)

    and ltSimulR = function
      | gq_, d_, [], [] -> false
      | gq_, d_, o_ :: l_, o'_ :: l'_ ->
          (ordLtR (gq_, d_, o_, o'_) && leSimulR (gq_, d_, l_, l'_))
          || (ordEqR (gq_, d_, o_, o'_) && ltSimulR (gq_, d_, l_, l'_))

    and leSimulR = function
      | gq_, d_, [], [] -> true
      | gq_, d_, o_ :: l_, o'_ :: l'_ ->
          ordLeR (gq_, d_, o_, o'_) && leSimulR (gq_, d_, l_, l'_)

    and ltAtomicR (gq_, d_, usVs_, usVs'_, sc, k) =
      ltAtomicRW (gq_, d_, Whnf.whnfEta usVs_, usVs'_, sc, k)

    and ltAtomicRW = function
      | gq_, d_, ((us_, ((I.Root _, s') as vs_)) as usVs_), usVs'_, sc, k ->
          ltR (gq_, d_, usVs_, usVs'_, sc, k)
      | ( ((g_, q_) as gq_),
          d_,
          ((I.Lam (_, u_), s1), (I.Pi ((dec_, _), v_), s2)),
          ((u'_, s1'), (v'_, s2')),
          sc,
          k ) ->
          let usVs'_ =
            ((u'_, I.comp (s1', I.shift)), (v'_, I.comp (s2', I.shift)))
          in
          let usVs_ = ((u_, I.dot1 s1), (v_, I.dot1 s2)) in
          let d'_ = shiftACtx d_ (function s -> I.comp (s, I.shift)) in
          ltAtomicR
            ( ( I.Decl (g_, N.decLUName (g_, I.decSub (dec_, s2))),
                I.Decl (q_, All) ),
              d'_,
              usVs_,
              usVs'_,
              sc,
              k )

    and leAtomicR (gq_, d_, usVs_, usVs'_, sc, k) =
      leAtomicRW (gq_, d_, Whnf.whnfEta usVs_, usVs'_, sc, k)

    and leAtomicRW = function
      | gq_, d_, ((us_, ((I.Root _, s') as vs_)) as usVs_), usVs'_, sc, k ->
          leR (gq_, d_, usVs_, usVs'_, sc, k)
      | ( ((g_, q_) as gq_),
          d_,
          ((I.Lam (_, u_), s1), (I.Pi ((dec_, _), v_), s2)),
          ((u'_, s1'), (v'_, s2')),
          sc,
          k ) ->
          let d'_ = shiftACtx d_ (function s -> I.comp (s, I.shift)) in
          let usVs'_ =
            ((u'_, I.comp (s1', I.shift)), (v'_, I.comp (s2', I.shift)))
          in
          let usVs_ = ((u_, I.dot1 s1), (v_, I.dot1 s2)) in
          leAtomicR
            ( ( I.Decl (g_, N.decLUName (g_, I.decSub (dec_, s2))),
                I.Decl (q_, All) ),
              d'_,
              usVs_,
              usVs'_,
              sc,
              k )

    and eqAtomicR (((g_, q_) as gq_), d_, usVs_, usVs'_, sc, k) =
      eqAtomicRW (gq_, d_, Whnf.whnfEta usVs_, Whnf.whnfEta usVs'_, sc, k)

    and eqAtomicRW = function
      | ( ((g_, q_) as gq_),
          d_,
          ((I.Lam (_, u_), s1), (I.Pi ((dec_, _), v_), s2)),
          ((I.Lam (_, u'_), s1'), (I.Pi ((dec'_, _), v'_), s2')),
          sc,
          k ) ->
          eqAtomicR
            ( ( I.Decl (g_, N.decLUName (g_, I.decSub (dec_, s2))),
                I.Decl (q_, All) ),
              shiftACtx d_ (function s -> I.comp (s, I.shift)),
              ((u_, I.dot1 s1'), (v_, I.dot1 s2')),
              ((u'_, I.dot1 s1'), (v'_, I.dot1 s2')),
              sc,
              k )
      | ( gq_,
          d_,
          (us_, ((I.Root _, s2) as vs_)),
          (us'_, ((I.Root _, s2') as vs'_)),
          sc,
          k ) ->
          eqR (gq_, d_, (us_, vs_), (us'_, vs'_), sc, k)
      | gq_, d_, (us_, vs_), (us'_, vs'_), sc, k -> false

    and ltR (((g_, q_) as gq_), d_, usVs_, usVs'_, sc, k) =
      ltRW (gq_, d_, usVs_, Whnf.whnfEta usVs'_, sc, k)

    and ltRW = function
      | ( gq_,
          d_,
          (us_, vs_),
          (((I.Root (I.Const c, s'_), s') as us'_), vs'_),
          sc,
          k ) -> begin
          if isAtomic (gq_, us'_) then
            k (gq_, d_, [], Less ((us_, vs_), (us'_, vs'_)), sc)
          else
            ltSpineR
              (gq_, d_, (us_, vs_), ((s'_, s'), (I.constType c, I.id)), sc, k)
        end
      | ( gq_,
          d_,
          (us_, vs_),
          (((I.Root (I.Def c, s'_), s') as us'_), vs'_),
          sc,
          k ) -> begin
          if isAtomic (gq_, us'_) then
            k (gq_, d_, [], Less ((us_, vs_), (us'_, vs'_)), sc)
          else
            ltSpineR
              (gq_, d_, (us_, vs_), ((s'_, s'), (I.constType c, I.id)), sc, k)
        end
      | ( ((g_, q_) as gq_),
          d_,
          (us_, vs_),
          (((I.Root (I.BVar n, s'_), s') as us'_), vs'_),
          sc,
          k ) -> begin
          if isAtomic (gq_, us'_) then
            k (gq_, d_, [], Less ((us_, vs_), (us'_, vs'_)), sc)
          else
            let (I.Dec (_, v'_)) = I.ctxDec (g_, n) in
            ltSpineR (gq_, d_, (us_, vs_), ((s'_, s'), (v'_, I.id)), sc, k)
        end
      | gq_, d_, _, ((I.EVar _, _), _), _, _ -> false
      | ( ((g_, q_) as gq_),
          d_,
          ((u_, s1), (v_, s2)),
          ( (I.Lam (I.Dec (_, v1'_), u'_), s1'),
            (I.Pi ((I.Dec (_, v2'_), _), v'_), s2') ),
          sc,
          k ) -> begin
          if Subordinate.equiv (I.targetFam v_, I.targetFam v1'_) then
            let x_ = I.newEVar (g_, I.EClo (v1'_, s1')) in
            let sc' = function
              | () -> begin
                  ignore (isParameter (q_, x_));
                  sc ()
                end
            in
            ltR
              ( gq_,
                d_,
                ((u_, s1), (v_, s2)),
                ((u'_, I.Dot (I.Exp x_, s1')), (v'_, I.Dot (I.Exp x_, s2'))),
                sc',
                k )
          else begin
            if Subordinate.below (I.targetFam v1'_, I.targetFam v_) then
              let x_ = I.newEVar (g_, I.EClo (v1'_, s1')) in
              ltR
                ( gq_,
                  d_,
                  ((u_, s1), (v_, s2)),
                  ((u'_, I.Dot (I.Exp x_, s1')), (v'_, I.Dot (I.Exp x_, s2'))),
                  sc,
                  k )
            else false
          end
        end

    and ltSpineR (gq_, d_, (us_, vs_), (ss'_, vs'_), sc, k) =
      ltSpineRW (gq_, d_, (us_, vs_), (ss'_, Whnf.whnf vs'_), sc, k)

    and ltSpineRW = function
      | gq_, d_, (us_, vs_), ((nil_, _), _), _, _ -> false
      | gq_, d_, (us_, vs_), ((I.SClo (s_, s'), s''), vs'_), sc, k ->
          ltSpineR (gq_, d_, (us_, vs_), ((s_, I.comp (s', s'')), vs'_), sc, k)
      | ( gq_,
          d_,
          (us_, vs_),
          ((I.App (u'_, s'_), s1'), (I.Pi ((I.Dec (_, v1'_), _), v2'_), s2')),
          sc,
          k ) ->
          leAtomicR (gq_, d_, (us_, vs_), ((u'_, s1'), (v1'_, s2')), sc, k)
          || ltSpineR
               ( gq_,
                 d_,
                 (us_, vs_),
                 ((s'_, s1'), (v2'_, I.Dot (I.Exp (I.EClo (u'_, s1')), s2'))),
                 sc,
                 k )

    and leR (gq_, d_, usVs_, usVs'_, sc, k) =
      leRW (gq_, d_, usVs_, Whnf.whnfEta usVs'_, sc, k)

    and leRW = function
      | ( ((g_, q_) as gq_),
          d_,
          ((u_, s1), (v_, s2)),
          ( (I.Lam (I.Dec (_, v1'_), u'_), s1'),
            (I.Pi ((I.Dec (_, v2'_), _), v'_), s2') ),
          sc,
          k ) -> begin
          if Subordinate.equiv (I.targetFam v_, I.targetFam v1'_) then
            let x_ = I.newEVar (g_, I.EClo (v1'_, s1')) in
            let sc' = function () -> isParameter (q_, x_) && sc () in
            leR
              ( gq_,
                d_,
                ((u_, s1), (v_, s2)),
                ((u'_, I.Dot (I.Exp x_, s1')), (v'_, I.Dot (I.Exp x_, s2'))),
                sc',
                k )
          else begin
            if Subordinate.below (I.targetFam v1'_, I.targetFam v_) then
              let x_ = I.newEVar (g_, I.EClo (v1'_, s1')) in
              leR
                ( gq_,
                  d_,
                  ((u_, s1), (v_, s2)),
                  ((u'_, I.Dot (I.Exp x_, s1')), (v'_, I.Dot (I.Exp x_, s2'))),
                  sc,
                  k )
            else false
          end
        end
      | gq_, d_, usVs_, usVs'_, sc, k ->
          ltR (gq_, d_, usVs_, usVs'_, sc, k)
          || eqR (gq_, d_, usVs_, usVs'_, sc, k)

    and eqR (((g_, q_) as gq_), d_, usVs_, usVs'_, sc, k) =
      Cs_manager.trail (function () -> eq (g_, usVs_, usVs'_) && sc ())
      || eqR' (gq_, d_, usVs_, usVs'_, sc, k)

    and eqR' = function
      | ( gq_,
          d_,
          (us_, ((I.Pi ((I.Dec (_, v2'_), _), v'_), s2') as vs_)),
          (us'_, ((I.Root _, s2'') as vs'_)),
          sc,
          k ) ->
          false
      | ( gq_,
          d_,
          (us_, ((I.Root _, s2') as vs_)),
          (us'_, ((I.Pi ((I.Dec (_, v2''_), _), v''_), s2'') as vs'_)),
          sc,
          k ) ->
          false
      | ( gq_,
          d_,
          (((I.Root (I.Const c, s_), s), vs_) as usVs_),
          (((I.Root (I.Const c', s'_), s'), vs'_) as usVs'_),
          sc,
          k ) -> begin
          if eqCid (c, c') then
            eqSpineR
              ( gq_,
                d_,
                ((s_, s), (I.constType c, I.id)),
                ((s'_, s'), (I.constType c', I.id)),
                sc,
                k )
          else false
        end
      | ( gq_,
          d_,
          (((I.Root (I.Const c, s_), s) as us_), vs_),
          (((I.Root (I.BVar n, s'_), s') as us'_), vs'_),
          sc,
          k ) -> begin
          if isAtomic (gq_, us'_) then
            k (gq_, d_, [], Eq ((us'_, vs'_), (us_, vs_)), sc)
          else false
        end
      | ( gq_,
          d_,
          (((I.Root (I.BVar n, s_), s) as us_), vs_),
          (((I.Root (I.Const c, s'_), s') as us'_), vs'_),
          sc,
          k ) -> begin
          if isAtomic (gq_, us_) then
            k (gq_, d_, [], Eq ((us_, vs_), (us'_, vs'_)), sc)
          else false
        end
      | ( gq_,
          d_,
          (((I.Root (I.Def c, s_), s), vs_) as usVs_),
          (((I.Root (I.Def c', s'_), s'), vs'_) as usVs'_),
          sc,
          k ) -> begin
          if eqCid (c, c') then
            eqSpineR
              ( gq_,
                d_,
                ((s_, s), (I.constType c, I.id)),
                ((s'_, s'), (I.constType c', I.id)),
                sc,
                k )
          else false
        end
      | ( gq_,
          d_,
          (((I.Root (I.Def c, s_), s) as us_), vs_),
          (((I.Root (I.BVar n, s'_), s') as us'_), vs'_),
          sc,
          k ) -> begin
          if isAtomic (gq_, us'_) then
            k (gq_, d_, [], Eq ((us'_, vs'_), (us_, vs_)), sc)
          else false
        end
      | ( gq_,
          d_,
          (((I.Root (I.BVar n, s_), s) as us_), vs_),
          (((I.Root (I.Def c, s'_), s') as us'_), vs'_),
          sc,
          k ) -> begin
          if isAtomic (gq_, us_) then
            k (gq_, d_, [], Eq ((us_, vs_), (us'_, vs'_)), sc)
          else false
        end
      | ( ((g_, q_) as gq_),
          d_,
          (((I.Root (I.BVar n, s_), s) as us_), vs_),
          (((I.Root (I.BVar n', s'_), s') as us'_), vs'_),
          sc,
          k ) -> begin
          if n = n' then
            let (I.Dec (_, v'_)) = I.ctxDec (g_, n) in
            eqSpineR
              (gq_, d_, ((s_, s), (v'_, I.id)), ((s'_, s'), (v'_, I.id)), sc, k)
          else k (gq_, d_, [], Eq ((us_, vs_), (us'_, vs'_)), sc)
        end
      | gq_, d_, usVs_, usVs'_, sc, k -> k (gq_, d_, [], Eq (usVs_, usVs'_), sc)

    and eqSpineR (gq_, d_, (ss_, vs_), (ss'_, vs'_), sc, k) =
      eqSpineRW (gq_, d_, (ss_, Whnf.whnf vs_), (ss'_, Whnf.whnf vs'_), sc, k)

    and eqSpineRW = function
      | gq_, d_, ((Nil, s), vs_), ((Nil, s'), vs'_), sc, k -> true
      | gq_, d_, ((I.SClo (s_, s'), s''), vs_), ssVs'_, sc, k ->
          eqSpineR (gq_, d_, ((s_, I.comp (s', s'')), vs_), ssVs'_, sc, k)
      | gq_, d_, ssVs_, ((I.SClo (s'_, s'), s''), vs'_), sc, k ->
          eqSpineR (gq_, d_, ssVs_, ((s'_, I.comp (s', s'')), vs'_), sc, k)
      | ( gq_,
          d_,
          ((I.App (u_, s_), s1), (I.Pi ((I.Dec (_, v1_), _), v2_), s2)),
          ((I.App (u'_, s'_), s1'), (I.Pi ((I.Dec (_, v1'_), _), v2'_), s2')),
          sc,
          k ) ->
          eqAtomicR
            (gq_, d_, ((u_, s1), (v1_, s2)), ((u'_, s1'), (v1'_, s2')), sc, k)
          && eqSpineR
               ( gq_,
                 d_,
                 ((s_, s1), (v2_, I.Dot (I.Exp (I.EClo (u_, s1)), s2))),
                 ((s'_, s1'), (v2'_, I.Dot (I.Exp (I.EClo (u'_, s1')), s2'))),
                 sc,
                 k )
      | gq_, d_, ssVs_, ssVs'_, sc, k -> false

    let rec leftDecompose = function
      | ((g_, q_) as gq_), [], d'_, p_ -> rightDecompose (gq_, d'_, p_)
      | gq_, Less (R.Arg usVs_, R.Arg usVs'_) :: d_, d'_, p_ ->
          ltAtomicL (gq_, d_, d'_, usVs_, usVs'_, p_)
      | gq_, Less (R.Lex o_, R.Lex o'_) :: d_, d'_, p_ ->
          ltLexL (gq_, d_, d'_, o_, o'_, p_)
      | gq_, Less (R.Simul o_, R.Simul o'_) :: d_, d'_, p_ ->
          ltSimulL (gq_, d_, d'_, o_, o'_, p_)
      | gq_, Leq (R.Arg usVs_, R.Arg usVs'_) :: d_, d'_, p_ ->
          leAtomicL (gq_, d_, d'_, usVs_, usVs'_, p_)
      | gq_, Leq (R.Lex o_, R.Lex o'_) :: d_, d'_, p_ ->
          leftDecompose (gq_, Less (R.Lex o_, R.Lex o'_) :: d_, d'_, p_)
          && leftDecompose (gq_, Eq (R.Lex o_, R.Lex o'_) :: d_, d'_, p_)
      | gq_, Leq (R.Simul o_, R.Simul o'_) :: d_, d'_, p_ ->
          leSimulL (gq_, d_, d'_, o_, o'_, p_)
      | gq_, Eq (R.Arg usVs_, R.Arg usVs'_) :: d_, d'_, p_ ->
          eqAtomicL (gq_, d_, d'_, usVs_, usVs'_, p_)
      | gq_, Eq (R.Lex o_, R.Lex o'_) :: d_, d'_, p_ ->
          eqsL (gq_, d_, d'_, o_, o'_, p_)
      | gq_, Eq (R.Simul o_, R.Simul o'_) :: d_, d'_, p_ ->
          eqsL (gq_, d_, d'_, o_, o'_, p_)
      | ((g_, q_) as gq_), Pi (dec_, o_) :: d_, d'_, p_ -> begin
          begin if !Global.chatter > 3 then begin
            print " Ignoring quantified order ";
            print (F.makestring_fmt (fmtPredicate (g_, Pi (dec_, o_))))
          end
          else ()
          end;
          leftDecompose (gq_, d_, d'_, p_)
        end

    and ltLexL = function
      | gq_, d_, d'_, [], [], p_ -> true
      | gq_, d_, d'_, o_ :: l_, o'_ :: l'_, p_ ->
          leftDecompose (gq_, Less (o_, o'_) :: d_, d'_, p_)
          && ltLexL (gq_, Eq (o_, o'_) :: d_, d'_, l_, l'_, p_)

    and eqsL = function
      | gq_, d_, d'_, [], [], p_ -> true
      | gq_, d_, d'_, o_ :: l_, o'_ :: l'_, p_ ->
          leftDecompose (gq_, Eq (o_, o'_) :: d_, d'_, p_)
          && eqsL (gq_, d_, d'_, l_, l'_, p_)

    and ltSimulL = function
      | gq_, d_, d'_, [], [], p_ -> leftDecompose (gq_, d_, d'_, p_)
      | gq_, d_, d'_, o_ :: l_, o'_ :: l'_, p_ ->
          leSimulL (gq_, Less (o_, o'_) :: d_, d'_, l_, l'_, p_)
          || ltSimulL (gq_, Eq (o_, o'_) :: d_, d'_, l_, l'_, p_)

    and leSimulL = function
      | gq_, d_, d'_, [], [], p_ -> leftDecompose (gq_, d_, d'_, p_)
      | gq_, d_, d'_, o_ :: l_, o'_ :: l'_, p_ ->
          leSimulL (gq_, Leq (o_, o'_) :: d_, d'_, l_, l'_, p_)

    and ltAtomicL (gq_, d_, d'_, usVs_, usVs'_, p_) =
      ltAtomicLW (gq_, d_, d'_, usVs_, Whnf.whnfEta usVs'_, p_)

    and ltAtomicLW = function
      | ((g_, q_) as gq_), d_, d'_, usVs_, (us'_, ((I.Root _, s') as vs'_)), p_
        ->
          ltL (gq_, d_, d'_, usVs_, (us'_, vs'_), p_)
      | ( ((g_, q_) as gq_),
          d_,
          d'_,
          ((u_, s1), (v_, s2)),
          ((I.Lam (_, u'_), s1'), (I.Pi ((dec'_, _), v'_), s2')),
          p_ ) ->
          let d1_ = shiftRCtx d_ (function s -> I.comp (s, I.shift)) in
          let d1'_ = shiftACtx d'_ (function s -> I.comp (s, I.shift)) in
          let usVs_ =
            ((u_, I.comp (s1, I.shift)), (v_, I.comp (s2, I.shift)))
          in
          let usVs'_ = ((u'_, I.dot1 s1'), (v'_, I.dot1 s2')) in
          let p'_ = shiftP p_ (function s -> I.comp (s, I.shift)) in
          ltAtomicL
            ( ( I.Decl (g_, N.decLUName (g_, I.decSub (dec'_, s2'))),
                I.Decl (q_, All) ),
              d1_,
              d1'_,
              usVs_,
              usVs'_,
              p'_ )

    and leAtomicL (gq_, d_, d'_, usVs_, usVs'_, p_) =
      leAtomicLW (gq_, d_, d'_, usVs_, Whnf.whnfEta usVs'_, p_)

    and leAtomicLW = function
      | gq_, d_, d'_, usVs_, (us'_, ((I.Root (h_, s_), s') as vs'_)), p_ ->
          leL (gq_, d_, d'_, usVs_, (us'_, vs'_), p_)
      | ( ((g_, q_) as gq_),
          d_,
          d'_,
          ((u_, s1), (v_, s2)),
          ((I.Lam (_, u'_), s1'), (I.Pi ((dec'_, _), v'_), s2')),
          p_ ) ->
          let d1_ = shiftRCtx d_ (function s -> I.comp (s, I.shift)) in
          let d1'_ = shiftACtx d'_ (function s -> I.comp (s, I.shift)) in
          let usVs_ =
            ((u_, I.comp (s1, I.shift)), (v_, I.comp (s2, I.shift)))
          in
          let usVs'_ = ((u'_, I.dot1 s1'), (v'_, I.dot1 s2')) in
          let p'_ = shiftP p_ (function s -> I.comp (s, I.shift)) in
          leAtomicL
            ( ( I.Decl (g_, N.decLUName (g_, I.decSub (dec'_, s2'))),
                I.Decl (q_, All) ),
              d1_,
              d1'_,
              usVs_,
              usVs'_,
              p'_ )

    and eqAtomicL (gq_, d_, d'_, usVs_, usVs'_, p_) =
      eqAtomicLW (gq_, d_, d'_, Whnf.whnfEta usVs_, Whnf.whnfEta usVs'_, p_)

    and eqAtomicLW = function
      | ( gq_,
          d_,
          d'_,
          (us_, ((I.Root _, s) as vs_)),
          (us'_, ((I.Root _, s') as vs'_)),
          p_ ) ->
          eqL (gq_, d_, d'_, (us_, vs_), (us'_, vs'_), p_)
      | ( gq_,
          d_,
          d'_,
          (us_, ((I.Root _, s) as vs_)),
          (us'_, ((I.Pi _, s') as vs'_)),
          p_ ) ->
          true
      | ( gq_,
          d_,
          d'_,
          (us_, ((I.Pi _, s) as vs_)),
          (us'_, ((I.Root _, s') as vs'_)),
          p_ ) ->
          true
      | ( gq_,
          d_,
          d'_,
          (us_, ((I.Pi _, s) as vs_)),
          (us'_, ((I.Pi _, s') as vs'_)),
          p_ ) ->
          leftDecompose (gq_, d_, Eq ((us_, vs_), (us'_, vs'_)) :: d'_, p_)

    and leL (gq_, d_, d'_, usVs_, usVs'_, p_) =
      ltAtomicL (gq_, d_, d'_, usVs_, usVs'_, p_)
      && eqAtomicL (gq_, d_, d'_, usVs_, usVs'_, p_)

    and ltL (gq_, d_, d'_, usVs_, (us'_, vs'_), p_) =
      ltLW (gq_, d_, d'_, usVs_, (Whnf.whnf us'_, vs'_), p_)

    and ltLW = function
      | ( ((g_, q_) as gq_),
          d_,
          d'_,
          usVs_,
          (((I.Root (I.BVar n, s'_), s') as us'_), vs'_),
          p_ ) -> begin
          if isAtomic (gq_, us'_) then
            leftDecompose (gq_, d_, Less (usVs_, (us'_, vs'_)) :: d'_, p_)
          else
            let (I.Dec (_, v'_)) = I.ctxDec (g_, n) in
            ltSpineL (gq_, d_, d'_, usVs_, ((s'_, s'), (v'_, I.id)), p_)
        end
      | gq_, d_, d'_, usVs_, ((I.Root (I.Const c, s'_), s'), vs'_), p_ ->
          ltSpineL (gq_, d_, d'_, usVs_, ((s'_, s'), (I.constType c, I.id)), p_)
      | gq_, d_, d'_, usVs_, ((I.Root (I.Def c, s'_), s'), vs'_), p_ ->
          ltSpineL (gq_, d_, d'_, usVs_, ((s'_, s'), (I.constType c, I.id)), p_)

    and ltSpineL (gq_, d_, d'_, usVs_, (ss'_, vs'_), p_) =
      ltSpineLW (gq_, d_, d'_, usVs_, (ss'_, Whnf.whnf vs'_), p_)

    and ltSpineLW = function
      | gq_, d_, d'_, usVs_, ((nil_, _), _), _ -> true
      | gq_, d_, d'_, usVs_, ((I.SClo (s_, s'), s''), vs'_), p_ ->
          ltSpineL (gq_, d_, d'_, usVs_, ((s_, I.comp (s', s'')), vs'_), p_)
      | ( gq_,
          d_,
          d'_,
          usVs_,
          ((I.App (u'_, s'_), s1'), (I.Pi ((I.Dec (_, v1'_), _), v2'_), s2')),
          p_ ) ->
          leAtomicL (gq_, d_, d'_, usVs_, ((u'_, s1'), (v1'_, s2')), p_)
          && ltSpineL
               ( gq_,
                 d_,
                 d'_,
                 usVs_,
                 ((s'_, s1'), (v2'_, I.Dot (I.Exp (I.EClo (u'_, s1')), s2'))),
                 p_ )

    and eqL (gq_, d_, d'_, usVs_, usVs'_, p_) =
      eqLW (gq_, d_, d'_, Whnf.whnfEta usVs_, Whnf.whnfEta usVs'_, p_)

    and eqLW = function
      | ( gq_,
          d_,
          d'_,
          (us_, ((I.Pi ((I.Dec (_, v2'_), _), v'_), s2') as vs_)),
          (us'_, ((I.Pi ((I.Dec (_, v2''_), _), v''_), s2'') as vs'_)),
          p_ ) ->
          leftDecompose (gq_, d_, Eq ((us_, vs_), (us'_, vs'_)) :: d'_, p_)
      | ( gq_,
          d_,
          d'_,
          (us_, ((I.Pi ((I.Dec (_, v2'_), _), v'_), s2') as vs_)),
          (us'_, ((I.Root _, s2'') as vs'_)),
          p_ ) ->
          true
      | ( gq_,
          d_,
          d'_,
          (us_, ((I.Root _, s2') as vs_)),
          (us'_, ((I.Pi ((I.Dec (_, v2''_), _), v''_), s2'') as vs'_)),
          p_ ) ->
          true
      | ( gq_,
          d_,
          d'_,
          (((I.Root (I.Const c, s_), s), vs_) as usVs_),
          (((I.Root (I.Const c', s'_), s'), vs'_) as usVs'_),
          p_ ) -> begin
          if eqCid (c, c') then
            eqSpineL
              ( gq_,
                d_,
                d'_,
                ((s_, s), (I.constType c, I.id)),
                ((s'_, s'), (I.constType c', I.id)),
                p_ )
          else true
        end
      | ( gq_,
          d_,
          d'_,
          (((I.Root (I.Const c, s_), s) as us_), vs_),
          (((I.Root (I.BVar n, s'_), s') as us'_), vs'_),
          p_ ) -> begin
          if isAtomic (gq_, us'_) then
            leftDecompose (gq_, d_, Eq ((us'_, vs'_), (us_, vs_)) :: d'_, p_)
          else true
        end
      | ( gq_,
          d_,
          d'_,
          (((I.Root (I.BVar n, s_), s) as us_), vs_),
          (((I.Root (I.Const c, s'_), s') as us'_), vs'_),
          p_ ) -> begin
          if isAtomic (gq_, us_) then
            leftDecompose (gq_, d_, Eq ((us_, vs_), (us'_, vs'_)) :: d'_, p_)
          else true
        end
      | ( gq_,
          d_,
          d'_,
          (((I.Root (I.Def c, s_), s), vs_) as usVs_),
          (((I.Root (I.Def c', s'_), s'), vs'_) as usVs'_),
          p_ ) -> begin
          if eqCid (c, c') then
            eqSpineL
              ( gq_,
                d_,
                d'_,
                ((s_, s), (I.constType c, I.id)),
                ((s'_, s'), (I.constType c', I.id)),
                p_ )
          else true
        end
      | ( gq_,
          d_,
          d'_,
          (((I.Root (I.Def c, s_), s) as us_), vs_),
          (((I.Root (I.BVar n, s'_), s') as us'_), vs'_),
          p_ ) -> begin
          if isAtomic (gq_, us'_) then
            leftDecompose (gq_, d_, Eq ((us'_, vs'_), (us_, vs_)) :: d'_, p_)
          else true
        end
      | ( gq_,
          d_,
          d'_,
          (((I.Root (I.BVar n, s_), s) as us_), vs_),
          (((I.Root (I.Def c, s'_), s') as us'_), vs'_),
          p_ ) -> begin
          if isAtomic (gq_, us_) then
            leftDecompose (gq_, d_, Eq ((us_, vs_), (us'_, vs'_)) :: d'_, p_)
          else true
        end
      | ( ((g_, q_) as gq_),
          d_,
          d'_,
          (((I.Root (I.BVar n, s_), s) as us_), vs_),
          (((I.Root (I.BVar n', s'_), s') as us'_), vs'_),
          p_ ) -> begin
          if n = n' then
            let (I.Dec (_, v'_)) = I.ctxDec (g_, n) in
            eqSpineL
              ( gq_,
                d_,
                d'_,
                ((s_, s), (v'_, I.id)),
                ((s'_, s'), (v'_, I.id)),
                p_ )
          else leftDecompose (gq_, d_, Eq ((us_, vs_), (us'_, vs'_)) :: d'_, p_)
        end
      | gq_, d_, d'_, usVs_, usVs'_, p_ ->
          leftDecompose (gq_, d_, Eq (usVs_, usVs'_) :: d'_, p_)

    and eqSpineL (gq_, d_, d'_, (ss_, vs_), (ss'_, vs'_), p_) =
      eqSpineLW (gq_, d_, d'_, (ss_, Whnf.whnf vs_), (ss'_, Whnf.whnf vs'_), p_)

    and eqSpineLW = function
      | gq_, d_, d'_, ((Nil, s), vs_), ((Nil, s'), vs'_), p_ ->
          leftDecompose (gq_, d_, d'_, p_)
      | gq_, d_, d'_, ((I.SClo (s_, s'), s''), vs_), ssVs'_, p_ ->
          eqSpineL (gq_, d_, d'_, ((s_, I.comp (s', s'')), vs_), ssVs'_, p_)
      | gq_, d_, d'_, ssVs_, ((I.SClo (s'_, s'), s''), vs'_), p_ ->
          eqSpineL (gq_, d_, d'_, ssVs_, ((s'_, I.comp (s', s'')), vs'_), p_)
      | ( gq_,
          d_,
          d'_,
          ((I.App (u_, s_), s1), (I.Pi ((I.Dec (_, v1_), _), v2_), s2)),
          ((I.App (u'_, s'_), s1'), (I.Pi ((I.Dec (_, v1'_), _), v2'_), s2')),
          p_ ) ->
          let d1_ =
            Eq (R.Arg ((u_, s1), (v1_, s2)), R.Arg ((u'_, s1'), (v1'_, s2')))
            :: d_
          in
          eqSpineL
            ( gq_,
              d1_,
              d'_,
              ((s_, s1), (v2_, I.Dot (I.Exp (I.EClo (u_, s1)), s2))),
              ((s'_, s1'), (v2'_, I.Dot (I.Exp (I.EClo (u'_, s1')), s2'))),
              p_ )

    let rec deduce (g_, q_, d_, p_) = leftDecompose ((g_, q_), d_, [], p_)
  end

  (* Reasoning about order relations *)
  (*
    Typing context        G
    mixed prefix context  Q  := . | All | Existental

    Orders                0  := U[s1] : V[s2] | Lex O1 ... On | Simul O1 ... On
    Order Relation        P  := O < O' | O <= O' | O = O'

    Atomic Order Relation P' := U[s1] : V[s2] <  U'[s1'] : V'[s2'] |
                                U[s1] : V[s2] <= U'[s1'] : V'[s2'] |
                                U[s1] : V[s2] =  U'[s1'] : V'[s2']

    Order Relation Ctx    D  := . | R , D
    Atomic Order Rel. Ctx D' := . | R',  D'

    Invariant:

    sometimes we write G |- P as an abbreviation

    if P = (O < O')    then G |- O and G |- O'
    if P = (O <= O')    then G |- O and G |- O'
    if P = (O = O')    then G |- O and G |- O'

    if O = Lex O1 .. On  then G |- O1 and ....G |- On
    if O = Simul O1 .. On  then G |- O1 and ....G |- On

    if O = U[s1] : V[s2]
      then     G : Q
           and G |- s1 : G1, G1 |- U : V1
           and G |- s2 : G2   G2 |- V : L
           and G |- U[s1] : V[s2]

  *)
  (*--------------------------------------------------------------------*)
  (* Printing atomic orders *)
  (*--------------------------------------------------------------------*)
  (* shifting substitutions *)
  (* shiftO O f = O'

      if O is an order
         then we shift the substitutions which are associated
         with its terms by applying f to it
    *)
  (*--------------------------------------------------------------------*)
  (* Printing *)
  (* F.String ""Pi predicate""  *)
  (*--------------------------------------------------------------------*)
  (* init () = true

       Invariant:
       The inital constraint continuation
    *)
  (* isParameter (Q, X) = B

       Invariant:
       If   G |- X : V
       and  G : Q
       then B holds iff X is unrestricted (uninstantiated and free
       of constraints, or lowered only) or instantiated to a universal parameter
    *)
  (* isFreeEVar (Us) = true
       iff Us represents a possibly lowered uninstantiated EVar.

       Invariant: it participated only in matching, not full unification
    *)
  (* constraints must be empty *)
  (* isAtomic (G, X) = true
       Invariant:
       If G |- X : V
       and G : Q
       then B holds iff X is an atomic term which is not a parameter
     *)
  (* should disallow orelse ? *)
  (*      | isAtomicW (GQ, (X as (I.EClo _))) = true    existential var  *)
  (*-----------------------------------------------------------*)
  (* eq (G, ((U, s1), (V, s2)), ((U', s1'), (V', s2')), sc) = B

       Invariant:
       B holds  iff
            G |- s1 : G1   G1 |- U : V1
       and  G |- s2 : G2   G2 |- V : L
       and  G |- U[s1] : V[s2]
       and  G |- s' : G3  G3 |- U' : V'
       and  U[s1] is unifiable with to U'[s']
       and  all restrictions in sc are satisfied
       and V[s2] is atomic
       and only U'[s'] contains EVars
    *)
  (* lookupEq (GQ, D, UsVs, UsVs', sc) = B

     B holds iff

     and  D is an atomic order relation ctx
     and  UsVs and UsVs' are atomic and may contain EVars

          G : Q
     and  G |- s1 : G1   G1 |- U : V1
     and  G |- s2 : G2   G2 |- V : L
     and  G |- U[s1] : V [s2]
     and  G |- s' : G3  G3 |- U' : V'

     if there exists Eq(UsVs1, UsVs1') in D
        s.t. UsVs1 unifies with UsVs and
             UsVs1' unifies with UsVs' and
             all restrictions in sc are satisfied
     or
     if there exists Eq(UsVs1, UsVs1') in D
        s.t. UsVs1' unifies with UsVs and
             UsVs1 unifies with UsVs' and
             all restrictions in sc are satisfied
             (symmetry)


    *)
  (* lookupLt (GQ, D, UsVs, UsVs', sc) = B

     B holds iff

     and  D is an atomic order relation ctx
     and  UsVs and UsVs' are atomic and may contain EVars

          G : Q
     and  G |- s1 : G1   G1 |- U : V1
     and  G |- s2 : G2   G2 |- V : L
     and  G |- U[s1] : V [s2]
     and  G |- s' : G3  G3 |- U' : V'

     if there exists Less(UsVs1, UsVs1') in D
        s.t. UsVs1 unifies with UsVs and
             UsVs1' unifies with UsVs' and
             all restrictions in sc are satisfied
    *)
  (*  eqAtomic (GQ, D, D', UsVs, UsVs', sc) = B

        B iff
            UsVs unifies with UsVs'                (identity)
        or  D, UsVs = UsVs', D' ---> UsVs = UsVs'  (ctx lookup)
        or  D, UsVs' = UsVs, D' ---> UsVs = UsVs'  (ctx lookup + symmetry)
        or  D, D' ---> UsVs = UsVs' by transitivity

     *)
  (* transEq (GQ, D, D', UsVs, UsVs', sc) = B

     B iff
        if D, UsVs' = UsVs1 ; D' ---> UsVs = UsVs'
          then  D, D' ---> UsVs = UsVs1            (transEq1)

        or

        if D, UsVs1 = UsVs'; D' ---> UsVs = UsVs'  (transEq2)
          then  D, D' ---> UsVs = UsVs1

       or

       if D, UsVs1 = UsVs'; D' ---> UsVs = UsVs'
         then D; UsVs1 = UsVs' D' ---> UsVs = UsVs'
   *)
  (* ltAtomic (GQ, D, D', UsVs, UsVs', sc) = B

     B iff
        if D, UsVs <UsVs' ; D' ---> UsVs < UsVs'   (identity)

        or

        if D, UsVs1 = UsVs'; D' ---> UsVs = UsVs'  (transEq2)
          then  D, D' ---> UsVs = UsVs1

       or

       if D, UsVs1 = UsVs'; D' ---> UsVs = UsVs'
         then D; UsVs1 = UsVs' D' ---> UsVs = UsVs'
   *)
  (* transLt (GQ, D, D', UsVs, UsVs', sc) = B

     B iff
        if D, UsVs' = UsVs1 ; D' ---> UsVs = UsVs'
          then  D, D' ---> UsVs = UsVs1            (transEq1)

        or

        if D, UsVs1 = UsVs'; D' ---> UsVs = UsVs'  (transEq2)
          then  D, D' ---> UsVs = UsVs1

       or

       if D, UsVs1 = UsVs'; D' ---> UsVs = UsVs'
         then D; UsVs1 = UsVs' D' ---> UsVs = UsVs'
   *)
  (* atomic (GQ, D, P) = B

     An atomic order context D' is maximally decomposed iff

          T := Root(c, Nil) | Root(n, Nil)
    and   T' := Root(c,S) | Root(n, S)
    and   all atomic order relations in D' are
          either T' < T or T1' = T1'

   An atomic order P' is maximally decomposed iff
          T := Root(c, nil) | Root(n, Nil)
    and   T' := Root(c,S) | Root(n, S)
    and   T' < T or T1 = T1

    Invariant:

    B iff
          D and P are maximally decomposed,
      and they may contain EVars
      and G : Q
      and G |- P
      and G |- D
      and D --> P

      *)
  (*-----------------------------------------------------------*)
  (* leftInstantiate ((G,Q), D, D', P, sc) = B

     B iff
           G : Q
       and G |- D
       and G |- D'
       and G |- P

       and  D is an atomic order relation ctx, which does not
              contain any EVars
       and  D' is an atomic order relation ctx, which may
              contain EVars
       and  P' is a atomic order relation

       and  D --> P

    D' accumulates all orders
    *)
  (* should never happen by invariant *)
  (* ltInstL ((G, Q), D, D', UsVs, UsVs', P, sc) = B
     Invariant:
       B holds  iff
            G : Q
       and  D is an atomic order relation ctx
       and  D' is an atomic order relation ctx
       and  P' is a atomic order relation

       and  G |- s1 : G1   G1 |- U : V1
       and  G |- s2 : G2   G2 |- V : L
       and  G |- U[s1] : V [s2]
       and  G |- s' : G3  G3 |- U' : V'
       and  sc is a constraint continuation representing restrictions on EVars
       and  V[s2] atomic
       and  only U[s1] contains EVars
       and  D, D', U[s1] < U'[s'] ---> P
    *)
  (* == I.targetFam V2' *)
  (* = I.newEVar (I.EClo (V2', s2')) *)
  (* enforces that X can only bound to parameter or remain uninstantiated *)
  (* = I.newEVar (I.EClo (V2', s2')) *)
  (* impossible, if additional invariant assumed (see ltW) *)
  (* leInstL ((G, Q), D, D', UsVs, UsVs', P', sc) = B
     Invariant:
       B holds  iff
            G : Q
       and  D is an atomic order relation ctx
       and  D' is an atomic order relation ctx
       and  P' is a atomic order relation

       and  G |- s1 : G1   G1 |- U : V1
       and  G |- s2 : G2   G2 |- V : L
       and  G |- U[s1] : V [s2]
       and  G |- s' : G3  G3 |- U' : V'
       and  sc is a constraint continuation representing restrictions on EVars
       and  V[s2] atomic
       and  only U[s1] contains EVars
       and  D, D', U[s1] <= U'[s'] ---> P'
    *)
  (* == I.targetFam V2' *)
  (* = I.newEVar (I.EClo (V2', s2')) *)
  (* enforces that X can only bound to parameter or remain uninstantiated *)
  (* = I.newEVar (I.EClo (V2', s2')) *)
  (* impossible, if additional invariant assumed (see ltW) *)
  (* eqInstL ((G, Q), D, D', UsVs, UsVs', P, sc) = B

     Invariant:
       B holds  iff
            G : Q
       and  D is an atomic order relation ctx
       and  D' is an atomic order relation ctx
       and  P' is a atomic order relation
       and  G |- s1 : G1   G1 |- U : V1
       and  G |- s2 : G2   G2 |- V : L
       and  G |- U[s1] : V [s2]
       and  G |- s' : G3  G3 |- U' : V'
       and  sc is a constraint continuation representing restrictions on EVars
       and  V[s2] atomic
       and  only U[s1] and U'[s'] contain EVars
       and  D, D', U[s1] = U'[s'] ---> P'
    *)
  (* = I.newEVar (I.EClo (V2', s2')) *)
  (* eqIL ((G, Q), D, D', UsVs, UsVs', P, sc) = B

     Invariant:
       B holds  iff
            G : Q
       and  D is an atomic order relation ctx
       and  D' is an atomic order relation ctx
       and  P' is a atomic order relation
       and  G |- s1 : G1   G1 |- U : V1
       and  G |- s2 : G2   G2 |- V : L
       and  G |- U[s1] : V [s2]
       and  G |- s' : G3  G3 |- U' : V'
       and  sc is a constraint continuation representing restrictions on EVars
       and  V[s2] atomic
       and  only U[s1] and U'[s'] contain EVars
       and  D, D', U[s1] = U'[s'] ---> P'
       and U, U' will be maximally unfolded
    *)
  (* (Us, Vs as (I.Pi _ , _)) and (Us', Vs' as (I.Root _, _))
           or the other way
         *)
  (*--------------------------------------------------------------*)
  (* rightDecompose (GQ, D', P) = B

    B iff
        G : Q
    and D is maximally unfolded, but does not contain any EVars
    and P is a order relation
    and G |- P
    and D --> P

    *)
  (* ordLtR (GQ, D, O1, O2) = B'

       Invariant:
       If   G : Q
       and  G |- O1 augmented subterm
       and  G |- O2 augmented subterm not containing any EVars
       then B' holds iff D --> O1 < O2
    *)
  (* ordLeR (GQ, D, O1, O2) = B'

       Invariant:
       If   G : Q
       and  G |- O1 augmented subterm
       and  G |- O2 augmented subterm not containing any EVars
       then B' holds iff D --> O1 <= O2
    *)
  (* ordEqR (GQ, D, O1, O2) = B'

       Invariant:
       If   G : Q
       and  G |- O1 augmented subterm
       and  G |- O2 augmented subterm not containing any EVars
       then B' holds iff D --> O1 = O2
    *)
  (* ordEqsR (GQ, D', L1, L2) = B'

       Invariant:
       If   G : Q
       and  G |- L1 list of augmented subterms
       and  G |- L2 list of augmented subterms not containing any EVars
       then B' holds iff D' --> L1 = L2
    *)
  (* ltLexR (GQ, D', L1, L2) = B'

       Invariant:
       If   G : Q
       and  G |- L1 list of augmented subterms
       and  G |- L2 list of augmented subterms not contianing any EVars
       then B' holds iff D' --> L1 is lexically smaller than L2
    *)
  (* ltSimulR (GQ, D, L1, L2) = B'

       Invariant:
       If   G : Q
       and  G |- L1 list of augmented subterms
       and  G |- L2 list of augmented subterms not contianing any EVars
       then B' holds iff D implies that L1 is simultaneously smaller than L2
    *)
  (* leSimulR (G, Q, L1, L2) = B'

       Invariant:
       If   G : Q
       and  G |- L1 list of augmented subterms
       and  G |- L2 list of augmented subterms not containing any EVars
       then B' holds iff D implies that L1 is simultaneously less than or equal to L2
    *)
  (*--------------------------------------------------------------*)
  (* Atomic Orders (Right) *)
  (* ltAtomicR (GQ, (D, D'), UsVs, UsVs', sc, k) = B
     Invariant:
       B' holds  iff
            G : Q
       and  G |- s1 : G1   G1 |- U : V1
       and  G |- s2 : G2   G2 |- V : L
       and  G |- U[s1] : V[s2]
       and  G |- s1' : G3   G3 |- U' : V1'
       and  G |- s2' : G4   G4 |- V' : L
       and  G |- U'[s1'] : V'[s2']
       and  D' implies U[s1] is a strict subterm of U'[s1']
       and  sc is a constraint continuation representing restrictions on EVars
       and only U'[s'] contains EVars
       and k is a continuation describing what happens when
           UsVs and UsVs' are maximally unfolded
    *)
  (* leAtomicR (GQ, D, UsVs, UsVs', sc, k) = B
     Invariant:
       B' holds  iff
            G : Q
       and  G |- s1 : G1   G1 |- U : V1
       and  G |- s2 : G2   G2 |- V : L
       and  G |- U[s1] : V[s2]
       and  G |- s1' : G3   G3 |- U' : V1'
       and  G |- s2' : G4   G4 |- V' : L
       and  G |- U'[s1'] : V'[s2']
       and  D implies U[s1] is a subterm of U'[s1']
       and  sc is a constraint continuation representing restrictions on EVars
       and only U'[s'] contains EVars
       and k is a continuation describing what happens when
           UsVs and UsVs' are maximally unfolded
    *)
  (* eqAtomicR (GQ, D, UsVs, UsVs', sc, k) = B
     Invariant:
       B' holds  iff
            G : Q
       and  G |- s1 : G1   G1 |- U : V1
       and  G |- s2 : G2   G2 |- V : L
       and  G |- U[s1] : V[s2]
       and  G |- s1' : G3   G3 |- U' : V1'
       and  G |- s2' : G4   G4 |- V' : L
       and  G |- U'[s1'] : V'[s2']
       and  D implies U[s1] is structurally equivalent to U'[s1']
       and  sc is a constraint continuation representing restrictions on EVars
       and only U'[s'] contains EVars
       and k is a continuation describing what happens when
           UsVs and UsVs' are maximally unfolded
    *)
  (* Dec = Dec' *)
  (* mismatch: not equal *)
  (* Fri Feb 25 21:26:39 2005 -fp !!! *)
  (* ltR (GQ, D, UsVs, UsVs', sc, k) = B

       Invariant:
       B' holds  iff
            G : Q
       and  G |- s1 : G1   G1 |- U : V1
       and  G |- s2 : G2   G2 |- V : L
       and  G |- U[s1] : V[s2]
       and  G |- s1' : G3   G3 |- U' : V1'
       and  G |- s2' : G4   G4 |- V' : L
       and  G |- U'[s1'] : V'[s2']
       and  D' --> U[s1] is a strict subterm of U'[s1']
       and  sc is a constraint continuation representing restrictions on EVars
       and only U'[s'] contains EVars
       and U'[s'] will be maximally unfolded
       and k is a continuation describing what happens when
           UsVs and UsVs' are maximally unfolded

    *)
  (* either leftInstantiate D or  atomic reasoning *)
  (* either leftInstantiate D or  atomic reasoning *)
  (* either leftInstantiate D or  atomic reasoning *)
  (* == I.targetFam V2' *)
  (* enforce that X is only instantiated to parameters *)
  (* = I.newEVar (I.EClo (V2', s2')) *)
  (* = I.newEVar (I.EClo (V2', s2')) *)
  (* possibly redundant if lhs always subordinate to rhs *)
  (* cannot happen Sat Apr 20 16:08:30 2002 -bp *)
  (* leR (GQ, D, UsVs, UsVs', sc, k) = B

       Invariant:
       B' holds  iff
            G : Q
       and  G |- s1 : G1   G1 |- U : V1
       and  G |- s2 : G2   G2 |- V : L
       and  G |- U[s1] : V[s2]
       and  G |- s1' : G3   G3 |- U' : V1'
       and  G |- s2' : G4   G4 |- V' : L
       and  G |- U'[s1'] : V'[s2']
       and  D' --> U[s1] is a subterm of U'[s1']
       and  sc is a constraint continuation representing restrictions on EVars
       and only U'[s'] contains EVars
       and U'[s'] will be maximally unfolded
    *)
  (* == I.targetFam V2' *)
  (* = I.newEVar (I.EClo (V2', s2')) *)
  (* enforces that X can only bound to parameter or remain uninstantiated *)
  (* = I.newEVar (I.EClo (V2', s2')) *)
  (* impossible, if additional invariant assumed (see ltW) *)
  (* eqR (GQ, D, UsVs, UsVs', sc, k) = B

       Invariant:
       B' holds  iff
            G : Q
       and  G |- s1 : G1   G1 |- U : V1
       and  G |- s2 : G2   G2 |- V : L
       and  G |- U[s1] : V[s2]
       and  G |- s1' : G3   G3 |- U' : V1'
       and  G |- s2' : G4   G4 |- V' : L
       and  G |- U'[s1'] : V'[s2']
       and  D' --> U[s1] = U'[s1']
       and  sc is a constraint continuation representing restrictions on EVars
       and only U'[s'] contains EVars
       and U'[s'] will be maximally unfolded
    *)
  (* either leftInstantiate D or atomic reasoning *)
  (* either leftInstantiate D or atomic reasoning *)
  (* either leftInstantiate D or atomic reasoning *)
  (* either leftInstantiate D or atomic reasoning *)
  (* either leftInstantiate D or atomic reasoning *)
  (* UsVs = Lam *)
  (* either leftInstantiate D or atomic reasoning *)
  (*--------------------------------------------------------------*)
  (* leftDecompose (G, Q, D, D', P) = B

      if G : Q and
         D --> P  where D might contain orders (lex and simul)

      then D' --> P
           where all orders in D' are atomic

      D' accumulates all orders which are maximally unfolded,
      but do not contain any EVars

      maximally unfolded orders not containing EVars are:

      Less: R < L

      L := Root(c, Nil) | Root(n, Nil)
      R := Root(c, S) | Root(n, S) | Lam(x:A, R)
      S := . | App(R, S)


      Eq : R = L
      R := Root(n, Nil) | Lam(x:A, R)
      L := Root(c, S) | Root(n, S) | Lam(x:A, R)
      S := . | App(R, S)

    *)
  (* less *)
  (* le *)
  (* eq *)
  (* drop assumption Pi D. P *)
  (*--------------------------------------------------------------*)
  (* Lexicographic and Simultanous Orders (left)*)
  (* If D, D', Lex O1, ....On < Lex O'1, ....O'n --> P
      then
            D, D', O1 < O1' --> P
        and D, D', O1 = O1', O2 < O2 --> P

        ...
        and D, D', O1 = O1', .., O_n-1 = O'_n-1, O_n < O'_n --> P
    *)
  (* If D, D', Lex O1, ....On = Lex O'1, ....O'n --> P
      If D, D', Simul O1, ....On = Simul O'1, ....O'n --> P
      then
            D, D', O1 = O1' --> P
        and D, D', O2 = O2' --> P

        ...
        and D, D', On = On' --> P
    *)
  (*--------------------------------------------------------------*)
  (* Atomic Orders (left) *)
  (* U := Root(c, S) | Root(n, S) | Lam(x:A, U) *)
  (* ltAtomicL (GQ as (G, Q), D, D', ((U, s1), (V, s2)), ((U', s1'), (V', s2')), P) = B

     B holds iff

            G : Q
       and  G |- s1 : G1   G1 |- U : V1
       and  G |- s2 : G2   G2 |- V : L
       and  G |- U[s1] : V[s2]
       and  G |- s1' : G3   G3 |- U' : V1'
       and  G |- s2' : G4   G4 |- V' : L
       and  G |- U'[s1'] : V'[s2']

       and  G |- D, D', (U[s1]:V[s2]) < U'[s1']:V'[s2']) --> P


       if G |- D, D', (Us:Vs) < (\x1:A1....\xn:An. U'[s1']: V'[s2']) --> P and
               (n >= 0)
       then
          G, a1:A1, .... an:An |-
             D^n, D'^n, (Us^n:Vs^n) < U'[a1... an . s1'^n]:V'[a1. ... . an . s2'^n] --> P^n

       where D^n, (Us^n, P^n) means all substitutions in D (U, P etc)
             are shifted by n
    *)
  (* see invariant for ltAtomic *)
  (*  *)
  (*--------------------------------------------------------------*)
  (* U' := Root(c, S) | Root(n, S) *)
  (* add definitions! *)
  (*  If D, D', U < Root(c, S) --> P
      then D, D', U <= S' --> P
   *)
  (*  eqL (GQ, D, D', UsVs, UsVs', P) = B

       B holds iff

            G : Q

       and  D is an Order relation ctx
       and  D' is an atomic order relation ctx
       and  P is a order relation

       and  G |- s1 : G1   G1 |- U : V1
       and  G |- s2 : G2   G2 |- V : L
       and  G |- U[s1] : V[s2]
       and  G |- s1' : G3   G3 |- U' : V1'
       and  G |- s2' : G4   G4 |- V' : L
       and  G |- U'[s1'] : V'[s2']

       and D, D', U[s1] = U'[s1'] --> P

       note: D, D', UsVs, UsVs' and P do not
             contain any EVars
   *)
  (*
     | eqLW (GQ, D, D', UsVs as ((I.Root (I.BVar n, I.Nil), s), Vs),
            UsVs' as ((I.Root (I.BVar n', I.Nil), s'), Vs'), P) =
         if (n = n')
           then leftDecompose (GQ, D, D', P)
         else
           leftDecompose (GQ, D, (Eq(UsVs, UsVs') :: D'), P)

*)
  (* UsVs = Lam *)
  (*--------------------------------------------------------------*)
  (* Infer: D --> P *)
  (* deduce (G, Q, D, P) = B

      B iff
         G :  Q
     and G |- D
     and G |- P
     and D implies P
    *)
  let deduce = deduce
  let shiftRCtx = shiftRCtx
  let shiftPred = shiftP
end
(*! sharing Origins.Paths = Paths !*)
(*! sharing Origins.IntSyn = IntSyn' !*)
(*! structure Cs_manager : CS_MANAGER !*)
(*! sharing Cs_manager.IntSyn = IntSyn' !*)
(* local *)
(* functor checking  *)

(* # 1 "src/terminate/checking.sml.ml" *)
