open! Basis
open! Global
open! Global.Global_
open! Trail
open! Trail.Trail_
open! Intsyn
open! Intsyn.Lambda_
open! Names
open! Names.Names_
open! Print
open! Print.Print_
open! Formatter
open! Formatter__Formatter_
open! Index
open! Index.Index_
open! Subordinate
open! Subordinate
open! Paths
open! Paths.Paths_
open! Solvers
open! Solvers.Solvers_

(* # 1 "src/terminate/Checking.sig.ml" *)
open! Basis

(* Reasoning about orders *)
(* Author: Brigitte Pientka *)
include CHECKING
(* signature CHECKING *)

(* # 1 "src/terminate/Checking.fun.ml" *)
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
  module Subordinate : Subordinate.Subordinate_.SUBORDINATE

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
  type quantifier = All | Exist | And of Paths.occ

  (* Quantifier to mark parameters *)
  (* Q ::= All                     *)
  (*     | Exist                   *)
  (*     | And                     *)
  (* If Q marks all parameters in a context G we write   G : Q               *)
  type 'a predicate =
    | Less of 'a * 'a
    | Leq of 'a * 'a
    | Eq of 'a * 'a
    | Pi of IntSyn.dec * 'a predicate

  (* Abbreviation *)
  type nonrec order = (IntSyn.eclo * IntSyn.eclo) Order.order

  (* reduction order assumptions (unordered) *)
  type nonrec rctx = order predicate list

  (* mixed prefix order contex *)
  type nonrec qctx = quantifier IntSyn.ctx

  open! struct
    module I = IntSyn
    module P = Paths
    module N = Names
    module F = Print.Formatter
    module R = Order
    module Unify = Checking__0.Unify
    module Subordinate = Checking__0.Subordinate

    let mkEClo (u, s) = I.EClo (u, s)

    let atomicPredToString (g_, a) = match a with
      | Less ((us_, _), (us', _)) ->
          (Print.expToString g_ (mkEClo us_) ^ " < ")
          ^ Print.expToString g_ (mkEClo us')
      | Leq ((us_, _), (us', _)) ->
          (Print.expToString g_ (mkEClo us_) ^ " <= ")
          ^ Print.expToString g_ (mkEClo us')
      | Eq ((us_, _), (us', _)) ->
          (Print.expToString g_ (mkEClo us_) ^ " = ")
          ^ Print.expToString g_ (mkEClo us')

    let rec atomicRCtxToString (g_, a) = match a with
      | [] -> " "
      | o_ :: [] -> atomicPredToString (g_, o_)
      | o_ :: d'_ ->
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

    let shiftRCtx rl_ f = map (function p -> shiftP p f) rl_

    let shiftArg arg__5 arg__6 =
      begin match (arg__5, arg__6) with
      | Less (((u1_, s1), (v1_, s1')), ((u2_, s2), (v2_, s2'))), f ->
          Less (((u1_, f s1), (v1_, f s1')), ((u2_, f s2), (v2_, f s2')))
      | Leq (((u1_, s1), (v1_, s1')), ((u2_, s2), (v2_, s2'))), f ->
          Leq (((u1_, f s1), (v1_, f s1')), ((u2_, f s2), (v2_, f s2')))
      | Eq (((u1_, s1), (v1_, s1')), ((u2_, s2), (v2_, s2'))), f ->
          Eq (((u1_, f s1), (v1_, f s1')), ((u2_, f s2), (v2_, f s2')))
      end

    let shiftACtx rl_ f = map (function p -> shiftArg p f) rl_

    let fmtOrder (g_, o_) =
      let rec fmtOrder' = function
        | R.Arg (((u_, s) as us_), ((v_, s') as vs_)) ->
            F.hbox
              [ F.string "("; Print.formatExp g_ (mkEClo us_); F.string ")" ]
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

    let fmtComparison (g_, o_, comp, o'_) =
      F.hOVbox0 1 0 1
        [
          fmtOrder (g_, o_); F.break; F.string comp; F.break; fmtOrder (g_, o'_);
        ]

    let rec fmtPredicate' (g_, a) = match a with
      | Less (o_, o'_) -> fmtComparison (g_, o_, "<", o'_)
      | Leq (o_, o'_) -> fmtComparison (g_, o_, "<=", o'_)
      | Eq (o_, o'_) -> fmtComparison (g_, o_, "=", o'_)
      | Pi (d_, p_) ->
          F.hbox [ F.string "Pi "; fmtPredicate' (I.Decl (g_, d_), p_) ]

    let fmtPredicate (g_, p_) = fmtPredicate' (Names.ctxName g_, p_)

    let rec fmtRGCtx' (g_, a) = match a with
      | [] -> ""
      | p_ :: [] -> F.makestring_fmt (fmtPredicate' (g_, p_))
      | p_ :: rl_ ->
          (F.makestring_fmt (fmtPredicate' (g_, p_)) ^ " ,")
          ^ fmtRGCtx' (g_, rl_)

    let fmtRGCtx (g_, rl_) = fmtRGCtx' (Names.ctxName g_, rl_)
    let init () = true
    let eqCid (c, c') = c = c'

    let conv (us_, vs_) (us', vs'_) =
      Conv.conv vs_ vs'_ && Conv.conv us_ us'

    let isUniversal = function All -> true | Exist -> false | exist' -> false
    let isExistential = function All -> false | Exist -> true | exist' -> true

    let rec isParameter (q_, x_) = isParameterW (q_, Whnf.whnf (x_, I.id))

    and isParameterW (q_, us_) =
      try isUniversal (I.ctxLookup q_ (Whnf.etaContract (mkEClo us_)))
      with Whnf.Eta -> isFreeEVar us_

    and isFreeEVar = function
      | I.EVar (_, _, _, { contents = [] }), _ -> true
      | I.Lam (d_, u_), s -> isFreeEVar (Whnf.whnf (u_, I.dot1 s))
      | _ -> false

    let rec isAtomic (gq, us_) = isAtomicW (gq, Whnf.whnf us_)

    and isAtomicW = function
      | gq, ((I.Root (I.Const c, s_) as x_), s) -> isAtomicS (gq, (s_, s))
      | gq, ((I.Root (I.Def c, s_) as x_), s) -> isAtomicS (gq, (s_, s))
      | ((g_, q_) as gq), ((I.Root (I.BVar n, s_) as x_), s) ->
          isExistential (I.ctxLookup q_ n) || isAtomicS (gq, (s_, s))
      | gq, _ -> false

    and isAtomicS (gq, a) = match a with
      | (I.Nil, _) -> true
      | (I.SClo (s_, s'), s'') -> isAtomicS (gq, (s_, I.comp s' s''))
      | (I.App (u'_, s'_), s1') -> false

    let eq (g_, (us_, vs_), (us', vs'_)) =
      Unify.unifiable g_ vs_ vs'_ && Unify.unifiable g_ us_ us'

    let rec lookupEq (a, b, usVs, usVs', sc) = match a, b with
      | gq, [] -> false
      | gq, Less (_, _) :: d_ ->
          lookupEq (gq, d_, usVs, usVs', sc)
      | ((g_, q_) as gq), Eq (usVs1, usVs1') :: d_ ->
          CsManager.trail (function () ->
              eq (g_, usVs1, usVs) && eq (g_, usVs1', usVs') && sc ())
          || CsManager.trail (function () ->
              eq (g_, usVs1, usVs') && eq (g_, usVs1', usVs) && sc ())
          || lookupEq (gq, d_, usVs, usVs', sc)

    let rec lookupLt (a, b, usVs, usVs', sc) = match a, b with
      | gq, [] -> false
      | gq, Eq (_, _) :: d_ ->
          lookupLt (gq, d_, usVs, usVs', sc)
      | ((g_, q_) as gq), Less (usVs1, usVs1') :: d_ ->
          CsManager.trail (function () ->
              eq (g_, usVs1, usVs) && eq (g_, usVs1', usVs') && sc ())
          || lookupLt (gq, d_, usVs, usVs', sc)

    let rec eqAtomic (a, d_, d'_, usVs, usVs', sc) = match a, d_ with
      | ((g_, q_) as gq), [] ->
          CsManager.trail (function () -> eq (g_, usVs, usVs') && sc ())
          || lookupEq (gq, d'_, usVs, usVs', sc)
      | ((g_, q_) as gq), d_ ->
          CsManager.trail (function () -> eq (g_, usVs, usVs') && sc ())
          || lookupEq (gq, d_, usVs, usVs', sc)
          || lookupEq (gq, d'_, usVs, usVs', sc)
          || transEq (gq, d_, d'_, usVs, usVs', sc)

    and transEq (a, b, d'_, usVs, usVs', sc) = match a, b, d'_ with
      | ((g_, q_) as gq), [], d_ -> false
      | ((g_, q_) as gq), Eq (usVs1, usVs1') :: d_, d'_ ->
          CsManager.trail (function () ->
              eq (g_, usVs1', usVs')
              && sc ()
              && eqAtomicR (gq, d_ @ d'_, usVs, usVs1, sc, atomic))
          || CsManager.trail (function () ->
              eq (g_, usVs1, usVs')
              && sc ()
              && eqAtomicR (gq, d_ @ d'_, usVs, usVs1', sc, atomic))
          || transEq (gq, d_, Eq (usVs1, usVs1') :: d'_, usVs, usVs', sc)
      | ((g_, q_) as gq), Less (usVs1, usVs1') :: d_, d'_ ->
          transEq (gq, d_, d'_, usVs, usVs', sc)

    and ltAtomic (a, d_, d'_, usVs, usVs', sc) = match a, d_ with
      | ((g_, q_) as gq), [] ->
          lookupLt (gq, d'_, usVs, usVs', sc)
      | ((g_, q_) as gq), d_ ->
          lookupLt (gq, d_, usVs, usVs', sc)
          || lookupLt (gq, d'_, usVs, usVs', sc)
          || transLt (gq, d_, d'_, usVs, usVs', sc)

    and transLt (a, b, d'_, usVs, usVs', sc) = match a, b, d'_ with
      | ((g_, q_) as gq), [], d_ -> false
      | ((g_, q_) as gq), Eq (usVs1, usVs1') :: d_, d'_ ->
          CsManager.trail (function () ->
              eq (g_, usVs1', usVs')
              && sc ()
              && ltAtomicR (gq, d_ @ d'_, usVs, usVs1, sc, atomic))
          || CsManager.trail (function () ->
              eq (g_, usVs1, usVs')
              && sc ()
              && ltAtomicR (gq, d_ @ d'_, usVs, usVs1', sc, atomic))
          || transLt (gq, d_, Eq (usVs1, usVs1') :: d'_, usVs, usVs', sc)
      | ((g_, q_) as gq), Less (usVs1, usVs1') :: d_, d'_ ->
          CsManager.trail (function () ->
              eq (g_, usVs1', usVs')
              && sc ()
              && eqAtomicR (gq, d_ @ d'_, usVs, usVs1, sc, atomic))
          || CsManager.trail (function () ->
              eq (g_, usVs1', usVs')
              && sc ()
              && ltAtomicR (gq, d_ @ d'_, usVs, usVs1, sc, atomic))
          || transLt (gq, d_, Less (usVs1, usVs1') :: d'_, usVs, usVs', sc)

    and atomic (gq, d_, d'_, a, sc) = match a with
      | Eq (usVs, usVs') ->
          eqAtomic (gq, d_, d'_, usVs, usVs', sc)
      | Less (usVs, usVs') ->
          ltAtomic (gq, d_, d'_, usVs, usVs', sc)

    and leftInstantiate (a, b, d'_, p_, sc) = match a, b with
      | ((g_, q_) as gq), [] ->
          begin if atomic (gq, d'_, [], p_, sc) then begin
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
      | gq, Less (usVs, usVs') :: d_ ->
          ltInstL (gq, d_, d'_, usVs, usVs', p_, sc)
      | gq, Leq (usVs, usVs') :: d_ ->
          leInstL (gq, d_, d'_, usVs, usVs', p_, sc)
      | gq, Eq (usVs, usVs') :: d_ ->
          eqInstL (gq, d_, d'_, usVs, usVs', p_, sc)

    and ltInstL (gq, d_, d'_, usVs, usVs', p'_, sc) =
      ltInstLW (gq, d_, d'_, (let a__, b__ = usVs in Whnf.whnfEta a__ b__), usVs', p'_, sc)

    and ltInstLW (a, d_, d'_, usVs, usVs', p'_, sc) = match a, usVs, usVs' with
      | ((g_, q_) as gq), ( (I.Lam ((I.Dec (_, v1_) as dec_), u_), s1),
            (I.Pi ((I.Dec (_, v2_), _), v_), s2) ), ((u'_, s1'), (v'_, s2')) ->
          begin if Subordinate.equiv (I.targetFam v'_) (I.targetFam v1_) then
            let x_ = I.newEVar g_ (I.EClo (v1_, s1)) in
            let sc' () = isParameter (q_, x_) && sc () in
            ltInstL
              ( (g_, q_),
                d_,
                d'_,
                ((u_, I.Dot (I.Exp x_, s1)), (v_, I.Dot (I.Exp x_, s2))),
                ((u'_, s1'), (v'_, s2')),
                p'_,
                sc' )
          else
            begin if Subordinate.below (I.targetFam v1_) (I.targetFam v'_) then
              let x_ = I.newEVar g_ (I.EClo (v1_, s1)) in
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
      | gq, usVs, usVs' ->
          leftInstantiate (gq, d_, Less (usVs, usVs') :: d'_, p'_, sc)

    and leInstL (gq, d_, d'_, usVs, usVs', p'_, sc) =
      leInstLW (gq, d_, d'_, (let a__, b__ = usVs in Whnf.whnfEta a__ b__), usVs', p'_, sc)

    and leInstLW (a, d_, d'_, usVs, usVs', p'_, sc) = match a, usVs, usVs', p'_ with
      | ((g_, q_) as gq), ( (I.Lam (I.Dec (_, v1_), u_), s1),
            (I.Pi ((I.Dec (_, v2_), _), v_), s2) ), ((u'_, s1'), (v'_, s2')), p'_ ->
          begin if Subordinate.equiv (I.targetFam v'_) (I.targetFam v1_) then
            let x_ = I.newEVar g_ (I.EClo (v1_, s1)) in
            let sc' () = isParameter (q_, x_) && sc () in
            leInstL
              ( (g_, q_),
                d_,
                d'_,
                ((u_, I.Dot (I.Exp x_, s1)), (v_, I.Dot (I.Exp x_, s2))),
                ((u'_, s1'), (v'_, s2')),
                p'_,
                sc' )
          else
            begin if Subordinate.below (I.targetFam v1_) (I.targetFam v'_) then
              let x_ = I.newEVar g_ (I.EClo (v1_, s1)) in
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
      | gq, usVs, usVs', p_ ->
          leftInstantiate (gq, d_, Less (usVs, usVs') :: d'_, p_, sc)

    and eqInstL (gq, d_, d'_, usVs, usVs', p'_, sc) =
      eqInstLW (gq, d_, d'_, (let a__, b__ = usVs in Whnf.whnfEta a__ b__), (let a__, b__ = usVs' in Whnf.whnfEta a__ b__), p'_, sc)

    and eqInstLW (a, d_, d'_, usVs, usVs', p'_, sc) = match a, usVs, usVs' with
      | ((g_, q_) as gq), ( (I.Lam (I.Dec (_, v1'), u'_), s1'),
            (I.Pi ((I.Dec (_, v2'), _), v'_), s2') ), ( (I.Lam (I.Dec (_, v1''), u''), s1''),
            (I.Pi ((I.Dec (_, v2''), _), v''), s2'') ) ->
          let x_ = I.newEVar g_ (I.EClo (v1'', s1'')) in
          eqInstL
            ( gq,
              d_,
              d'_,
              ((u'_, I.Dot (I.Exp x_, s1')), (v'_, I.Dot (I.Exp x_, s2'))),
              ((u'', I.Dot (I.Exp x_, s1'')), (v'', I.Dot (I.Exp x_, s2''))),
              p'_,
              function
              | () -> begin
                  ignore (isParameter (q_, x_));
                  sc ()
                end )
      | gq, usVs, usVs' ->
          eqIL (gq, d_, d'_, usVs, usVs', p'_, sc)

    and eqIL (a, d_, d'_, b, d, p'_, sc) = match a, b, d with
      | ((g_, q_) as gq), (((I.Root (I.Const c, s_), s), vs_) as usVs), (((I.Root (I.Const c', s'_), s'), vs'_) as usVs') ->
          begin if eqCid (c, c') then
            eqSpineIL
              ( gq,
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
                    ^ atomicRCtxToString (g_, Eq (usVs, usVs') :: d_))
                   ^ atomicRCtxToString (g_, d'_))
                  ^ " ---> ")
                 ^ atomicPredToString (g_, p'_))
                ^ "\n")
            else ()
            end;
            true
          end
          end
      | ((g_, q_) as gq), (((I.Root (I.Def c, s_), s), vs_) as usVs), (((I.Root (I.Def c', s'_), s'), vs'_) as usVs') ->
          begin if eqCid (c, c') then
            eqSpineIL
              ( gq,
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
                    ^ atomicRCtxToString (g_, Eq (usVs, usVs') :: d_))
                   ^ atomicRCtxToString (g_, d'_))
                  ^ " ---> ")
                 ^ atomicPredToString (g_, p'_))
                ^ "\n")
            else ()
            end;
            true
          end
          end
      | ((g_, q_) as gq), (((I.Root (I.Const c, s_), s) as us_), vs_), (((I.Root (I.BVar n, s'_), s') as us'), vs'_) ->
          begin if isAtomic (gq, us') then
            leftInstantiate
              (gq, d_, Eq ((us', vs'_), (us_, vs_)) :: d'_, p'_, sc)
          else begin
            begin if !Global.chatter > 4 then
              print
                (((((" Proved: "
                    ^ atomicRCtxToString (g_, Eq ((us_, vs_), (us', vs'_)) :: d_)
                    )
                   ^ atomicRCtxToString (g_, d'_))
                  ^ " ---> ")
                 ^ atomicPredToString (g_, p'_))
                ^ "\n")
            else ()
            end;
            true
          end
          end
      | ((g_, q_) as gq), (((I.Root (I.Def c, s_), s) as us_), vs_), (((I.Root (I.BVar n, s'_), s') as us'), vs'_) ->
          begin if isAtomic (gq, us') then
            leftInstantiate
              (gq, d_, Eq ((us', vs'_), (us_, vs_)) :: d'_, p'_, sc)
          else begin
            begin if !Global.chatter > 4 then
              print
                (((((" Proved: "
                    ^ atomicRCtxToString (g_, Eq ((us_, vs_), (us', vs'_)) :: d_)
                    )
                   ^ atomicRCtxToString (g_, d'_))
                  ^ " ---> ")
                 ^ atomicPredToString (g_, p'_))
                ^ "\n")
            else ()
            end;
            true
          end
          end
      | ((g_, q_) as gq), (((I.Root (I.BVar n, s_), s) as us_), vs_), (((I.Root (I.Def c, s'_), s') as us'), vs'_) ->
          begin if isAtomic (gq, us_) then
            leftInstantiate
              (gq, d_, Eq ((us_, vs_), (us', vs'_)) :: d'_, p'_, sc)
          else begin
            begin if !Global.chatter > 4 then
              print
                (((((" Proved: "
                    ^ atomicRCtxToString
                        (g_, Eq ((us_, vs_), (us', vs'_)) :: d'_))
                   ^ atomicRCtxToString (g_, d'_))
                  ^ " ---> ")
                 ^ atomicPredToString (g_, p'_))
                ^ "\n")
            else ()
            end;
            true
          end
          end
      | ((g_, q_) as gq), (((I.Root (I.BVar n, s_), s) as us_), vs_), (((I.Root (I.Const c, s'_), s') as us'), vs'_) ->
          begin if isAtomic (gq, us_) then
            leftInstantiate
              (gq, d_, Eq ((us_, vs_), (us', vs'_)) :: d'_, p'_, sc)
          else begin
            begin if !Global.chatter > 4 then
              print
                (((((" Proved: "
                    ^ atomicRCtxToString
                        (g_, Eq ((us_, vs_), (us', vs'_)) :: d'_))
                   ^ atomicRCtxToString (g_, d'_))
                  ^ " ---> ")
                 ^ atomicPredToString (g_, p'_))
                ^ "\n")
            else ()
            end;
            true
          end
          end
      | ((g_, q_) as gq), (((I.Root (I.BVar n, s_), s) as us_), vs_), (((I.Root (I.BVar n', s'_), s') as us'), vs'_) ->
          begin if n = n' then
            let (I.Dec (_, v'_)) = I.ctxDec g_ n in
            eqSpineIL
              ( gq,
                d_,
                d'_,
                ((s_, s), (v'_, I.id)),
                ((s'_, s'), (v'_, I.id)),
                p'_,
                sc )
          else
            leftInstantiate
              (gq, d_, Eq ((us_, vs_), (us', vs'_)) :: d'_, p'_, sc)
          end
      | ((g_, q_) as gq), usVs, usVs' -> begin
          begin if !Global.chatter > 4 then
            print
              (((((" Proved: " ^ atomicRCtxToString (g_, Eq (usVs, usVs') :: d_))
                 ^ atomicRCtxToString (g_, d'_))
                ^ " ---> ")
               ^ atomicPredToString (g_, p'_))
              ^ "\n")
          else ()
          end;
          true
        end

    and eqSpineIL (gq, d_, d'_, (ss_, vs_), (ss'_, vs'_), p'_, sc) =
      eqSpineILW
        (gq, d_, d'_, (ss_, Whnf.whnf vs_), (ss'_, Whnf.whnf vs'_), p'_, sc)

    and eqSpineILW (gq, d_, d'_, ssVs, ssVs', p'_, sc) = match ssVs, ssVs' with
      | ((Nil, s), vs_), ((Nil, s'), vs'_) ->
          leftInstantiate (gq, d_, d'_, p'_, sc)
      | ((I.SClo (s_, s'), s''), vs_), ssVs' ->
          eqSpineIL (gq, d_, d'_, ((s_, I.comp s' s''), vs_), ssVs', p'_, sc)
      | ssVs, ((I.SClo (s'_, s'), s''), vs'_) ->
          eqSpineIL (gq, d_, d'_, ssVs, ((s'_, I.comp s' s''), vs'_), p'_, sc)
      | ((I.App (u_, s_), s1), (I.Pi ((I.Dec (_, v1_), _), v2_), s2)), ((I.App (u'_, s'_), s1'), (I.Pi ((I.Dec (_, v1'), _), v2'), s2')) ->
          let d1_ =
            Eq (((u_, s1), (v1_, s2)), ((u'_, s1'), (v1', s2'))) :: d_
          in
          eqSpineIL
            ( gq,
              d1_,
              d'_,
              ((s_, s1), (v2_, I.Dot (I.Exp (I.EClo (u_, s1)), s2))),
              ((s'_, s1'), (v2', I.Dot (I.Exp (I.EClo (u'_, s1')), s2'))),
              p'_,
              sc )

    and rightDecompose (gq, d'_, a) = match a with
      | Less (o_, o'_) -> ordLtR (gq, d'_, o_, o'_)
      | Leq (o_, o'_) -> ordLeR (gq, d'_, o_, o'_)
      | Eq (o_, o'_) -> ordEqR (gq, d'_, o_, o'_)

    and ordLtR (gq, d'_, a, b) = match a, b with
      | R.Arg usVs, R.Arg usVs' ->
          ltAtomicR (gq, d'_, usVs, usVs', init, leftInstantiate)
      | R.Lex o_, R.Lex o'_ -> ltLexR (gq, d'_, o_, o'_)
      | R.Simul o_, R.Simul o'_ -> ltSimulR (gq, d'_, o_, o'_)

    and ordLeR (gq, d'_, a, b) = match a, b with
      | R.Arg usVs, R.Arg usVs' ->
          leAtomicR (gq, d'_, usVs, usVs', init, leftInstantiate)
      | R.Lex o_, R.Lex o'_ ->
          ltLexR (gq, d'_, o_, o'_) || ordEqsR (gq, d'_, o_, o'_)
      | R.Simul o_, R.Simul o'_ -> leSimulR (gq, d'_, o_, o'_)

    and ordEqR (gq, d'_, a, b) = match a, b with
      | R.Arg usVs, R.Arg usVs' ->
          conv usVs usVs'
          || eqAtomicR (gq, d'_, usVs, usVs', init, leftInstantiate)
      | R.Lex o_, R.Lex o'_ -> ordEqsR (gq, d'_, o_, o'_)
      | R.Simul o_, R.Simul o'_ -> ordEqsR (gq, d'_, o_, o'_)

    and ordEqsR (gq, d'_, a, b) = match a, b with
      | [], [] -> true
      | o_ :: l_, o'_ :: l'_ ->
          ordEqR (gq, d'_, o_, o'_) && ordEqsR (gq, d'_, l_, l'_)

    and ltLexR (gq, d'_, a, b) = match a, b with
      | [], [] -> false
      | o_ :: l_, o'_ :: l'_ ->
          ordLtR (gq, d'_, o_, o'_)
          || (ordEqR (gq, d'_, o_, o'_) && ltLexR (gq, d'_, l_, l'_))

    and leLexR (gq, d'_, l_, l'_) =
      ltLexR (gq, d'_, l_, l'_) || ordEqsR (gq, d'_, l_, l'_)

    and ltSimulR (gq, d_, a, b) = match a, b with
      | [], [] -> false
      | o_ :: l_, o'_ :: l'_ ->
          (ordLtR (gq, d_, o_, o'_) && leSimulR (gq, d_, l_, l'_))
          || (ordEqR (gq, d_, o_, o'_) && ltSimulR (gq, d_, l_, l'_))

    and leSimulR (gq, d_, a, b) = match a, b with
      | [], [] -> true
      | o_ :: l_, o'_ :: l'_ ->
          ordLeR (gq, d_, o_, o'_) && leSimulR (gq, d_, l_, l'_)

    and ltAtomicR (gq, d_, usVs, usVs', sc, k) =
      ltAtomicRW (gq, d_, (let a__, b__ = usVs in Whnf.whnfEta a__ b__), usVs', sc, k)

    and ltAtomicRW (a, d_, b, c, sc, k) = match a, b, c with
      | gq, ((us_, ((I.Root _, s') as vs_)) as usVs), usVs' ->
          ltR (gq, d_, usVs, usVs', sc, k)
      | ((g_, q_) as gq), ((I.Lam (_, u_), s1), (I.Pi ((dec_, _), v_), s2)), ((u'_, s1'), (v'_, s2')) ->
          let usVs' =
            ((u'_, I.comp s1' I.shift), (v'_, I.comp s2' I.shift))
          in
          let usVs = ((u_, I.dot1 s1), (v_, I.dot1 s2)) in
          let d'_ = shiftACtx d_ (function s -> I.comp s I.shift) in
          ltAtomicR
            ( ( I.Decl (g_, N.decLUName g_ (I.decSub dec_ s2)),
                I.Decl (q_, All) ),
              d'_,
              usVs,
              usVs',
              sc,
              k )

    and leAtomicR (gq, d_, usVs, usVs', sc, k) =
      leAtomicRW (gq, d_, (let a__, b__ = usVs in Whnf.whnfEta a__ b__), usVs', sc, k)

    and leAtomicRW (a, d_, b, c, sc, k) = match a, b, c with
      | gq, ((us_, ((I.Root _, s') as vs_)) as usVs), usVs' ->
          leR (gq, d_, usVs, usVs', sc, k)
      | ((g_, q_) as gq), ((I.Lam (_, u_), s1), (I.Pi ((dec_, _), v_), s2)), ((u'_, s1'), (v'_, s2')) ->
          let d'_ = shiftACtx d_ (function s -> I.comp s I.shift) in
          let usVs' =
            ((u'_, I.comp s1' I.shift), (v'_, I.comp s2' I.shift))
          in
          let usVs = ((u_, I.dot1 s1), (v_, I.dot1 s2)) in
          leAtomicR
            ( ( I.Decl (g_, N.decLUName g_ (I.decSub dec_ s2)),
                I.Decl (q_, All) ),
              d'_,
              usVs,
              usVs',
              sc,
              k )

    and eqAtomicR (((g_, q_) as gq), d_, usVs, usVs', sc, k) =
      eqAtomicRW (gq, d_, (let a__, b__ = usVs in Whnf.whnfEta a__ b__), (let a__, b__ = usVs' in Whnf.whnfEta a__ b__), sc, k)

    and eqAtomicRW (a, d_, b, c, sc, k) = match a, b, c with
      | ((g_, q_) as gq), ((I.Lam (_, u_), s1), (I.Pi ((dec_, _), v_), s2)), ((I.Lam (_, u'_), s1'), (I.Pi ((dec', _), v'_), s2')) ->
          eqAtomicR
            ( ( I.Decl (g_, N.decLUName g_ (I.decSub dec_ s2)),
                I.Decl (q_, All) ),
              shiftACtx d_ (function s -> I.comp s I.shift),
              ((u_, I.dot1 s1'), (v_, I.dot1 s2')),
              ((u'_, I.dot1 s1'), (v'_, I.dot1 s2')),
              sc,
              k )
      | gq, (us_, ((I.Root _, s2) as vs_)), (us', ((I.Root _, s2') as vs'_)) ->
          eqR (gq, d_, (us_, vs_), (us', vs'_), sc, k)
      | gq, (us_, vs_), (us', vs'_) -> false

    and ltR (((g_, q_) as gq), d_, usVs, usVs', sc, k) =
      ltRW (gq, d_, usVs, (let a__, b__ = usVs' in Whnf.whnfEta a__ b__), sc, k)

    and ltRW = function
      | ( gq,
          d_,
          (us_, vs_),
          (((I.Root (I.Const c, s'_), s') as us'), vs'_),
          sc,
          k ) ->
          begin if isAtomic (gq, us') then
            k (gq, d_, [], Less ((us_, vs_), (us', vs'_)), sc)
          else
            ltSpineR
              (gq, d_, (us_, vs_), ((s'_, s'), (I.constType c, I.id)), sc, k)
          end
      | gq, d_, (us_, vs_), (((I.Root (I.Def c, s'_), s') as us'), vs'_), sc, k
        ->
          begin if isAtomic (gq, us') then
            k (gq, d_, [], Less ((us_, vs_), (us', vs'_)), sc)
          else
            ltSpineR
              (gq, d_, (us_, vs_), ((s'_, s'), (I.constType c, I.id)), sc, k)
          end
      | ( ((g_, q_) as gq),
          d_,
          (us_, vs_),
          (((I.Root (I.BVar n, s'_), s') as us'), vs'_),
          sc,
          k ) ->
          begin if isAtomic (gq, us') then
            k (gq, d_, [], Less ((us_, vs_), (us', vs'_)), sc)
          else
            let (I.Dec (_, v'_)) = I.ctxDec g_ n in
            ltSpineR (gq, d_, (us_, vs_), ((s'_, s'), (v'_, I.id)), sc, k)
          end
      | gq, d_, _, ((I.EVar _, _), _), _, _ -> false
      | ( ((g_, q_) as gq),
          d_,
          ((u_, s1), (v_, s2)),
          ( (I.Lam (I.Dec (_, v1'), u'_), s1'),
            (I.Pi ((I.Dec (_, v2'), _), v'_), s2') ),
          sc,
          k ) ->
          begin if Subordinate.equiv (I.targetFam v_) (I.targetFam v1') then
            let x_ = I.newEVar g_ (I.EClo (v1', s1')) in
            let sc' = function
              | () -> begin
                  ignore (isParameter (q_, x_));
                  sc ()
                end
            in
            ltR
              ( gq,
                d_,
                ((u_, s1), (v_, s2)),
                ((u'_, I.Dot (I.Exp x_, s1')), (v'_, I.Dot (I.Exp x_, s2'))),
                sc',
                k )
          else
            begin if Subordinate.below (I.targetFam v1') (I.targetFam v_) then
              let x_ = I.newEVar g_ (I.EClo (v1', s1')) in
              ltR
                ( gq,
                  d_,
                  ((u_, s1), (v_, s2)),
                  ((u'_, I.Dot (I.Exp x_, s1')), (v'_, I.Dot (I.Exp x_, s2'))),
                  sc,
                  k )
            else false
            end
          end

    and ltSpineR (gq, d_, (us_, vs_), (ss'_, vs'_), sc, k) =
      ltSpineRW (gq, d_, (us_, vs_), (ss'_, Whnf.whnf vs'_), sc, k)

    and ltSpineRW = function
      | gq, d_, (us_, vs_), ((I.Nil, _), _), _, _ -> false
      | gq, d_, (us_, vs_), ((I.SClo (s_, s'), s''), vs'_), sc, k ->
          ltSpineR (gq, d_, (us_, vs_), ((s_, I.comp s' s''), vs'_), sc, k)
      | ( gq,
          d_,
          (us_, vs_),
          ((I.App (u'_, s'_), s1'), (I.Pi ((I.Dec (_, v1'), _), v2'), s2')),
          sc,
          k ) ->
          leAtomicR (gq, d_, (us_, vs_), ((u'_, s1'), (v1', s2')), sc, k)
          || ltSpineR
               ( gq,
                 d_,
                 (us_, vs_),
                 ((s'_, s1'), (v2', I.Dot (I.Exp (I.EClo (u'_, s1')), s2'))),
                 sc,
                 k )

    and leR (gq, d_, usVs, usVs', sc, k) =
      leRW (gq, d_, usVs, (let a__, b__ = usVs' in Whnf.whnfEta a__ b__), sc, k)

    and leRW (a, d_, usVs, usVs', sc, k) = match a, usVs, usVs' with
      | ((g_, q_) as gq), ((u_, s1), (v_, s2)), ( (I.Lam (I.Dec (_, v1'), u'_), s1'),
            (I.Pi ((I.Dec (_, v2'), _), v'_), s2') ) ->
          begin if Subordinate.equiv (I.targetFam v_) (I.targetFam v1') then
            let x_ = I.newEVar g_ (I.EClo (v1', s1')) in
            let sc' () = isParameter (q_, x_) && sc () in
            leR
              ( gq,
                d_,
                ((u_, s1), (v_, s2)),
                ((u'_, I.Dot (I.Exp x_, s1')), (v'_, I.Dot (I.Exp x_, s2'))),
                sc',
                k )
          else
            begin if Subordinate.below (I.targetFam v1') (I.targetFam v_) then
              let x_ = I.newEVar g_ (I.EClo (v1', s1')) in
              leR
                ( gq,
                  d_,
                  ((u_, s1), (v_, s2)),
                  ((u'_, I.Dot (I.Exp x_, s1')), (v'_, I.Dot (I.Exp x_, s2'))),
                  sc,
                  k )
            else false
            end
          end
      | gq, usVs, usVs' ->
          ltR (gq, d_, usVs, usVs', sc, k) || eqR (gq, d_, usVs, usVs', sc, k)

    and eqR (((g_, q_) as gq), d_, usVs, usVs', sc, k) =
      CsManager.trail (function () -> eq (g_, usVs, usVs') && sc ())
      || eqR' (gq, d_, usVs, usVs', sc, k)

    and eqR' (a, d_, b, d, sc, k) = match a, b, d with
      | gq, (us_, ((I.Pi ((I.Dec (_, v2'), _), v'_), s2') as vs_)), (us', ((I.Root _, s2'') as vs'_)) ->
          false
      | gq, (us_, ((I.Root _, s2') as vs_)), (us', ((I.Pi ((I.Dec (_, v2''), _), v''), s2'') as vs'_)) ->
          false
      | gq, (((I.Root (I.Const c, s_), s), vs_) as usVs), (((I.Root (I.Const c', s'_), s'), vs'_) as usVs') ->
          begin if eqCid (c, c') then
            eqSpineR
              ( gq,
                d_,
                ((s_, s), (I.constType c, I.id)),
                ((s'_, s'), (I.constType c', I.id)),
                sc,
                k )
          else false
          end
      | gq, (((I.Root (I.Const c, s_), s) as us_), vs_), (((I.Root (I.BVar n, s'_), s') as us'), vs'_) ->
          begin if isAtomic (gq, us') then
            k (gq, d_, [], Eq ((us', vs'_), (us_, vs_)), sc)
          else false
          end
      | gq, (((I.Root (I.BVar n, s_), s) as us_), vs_), (((I.Root (I.Const c, s'_), s') as us'), vs'_) ->
          begin if isAtomic (gq, us_) then
            k (gq, d_, [], Eq ((us_, vs_), (us', vs'_)), sc)
          else false
          end
      | gq, (((I.Root (I.Def c, s_), s), vs_) as usVs), (((I.Root (I.Def c', s'_), s'), vs'_) as usVs') ->
          begin if eqCid (c, c') then
            eqSpineR
              ( gq,
                d_,
                ((s_, s), (I.constType c, I.id)),
                ((s'_, s'), (I.constType c', I.id)),
                sc,
                k )
          else false
          end
      | gq, (((I.Root (I.Def c, s_), s) as us_), vs_), (((I.Root (I.BVar n, s'_), s') as us'), vs'_) ->
          begin if isAtomic (gq, us') then
            k (gq, d_, [], Eq ((us', vs'_), (us_, vs_)), sc)
          else false
          end
      | gq, (((I.Root (I.BVar n, s_), s) as us_), vs_), (((I.Root (I.Def c, s'_), s') as us'), vs'_) ->
          begin if isAtomic (gq, us_) then
            k (gq, d_, [], Eq ((us_, vs_), (us', vs'_)), sc)
          else false
          end
      | ((g_, q_) as gq), (((I.Root (I.BVar n, s_), s) as us_), vs_), (((I.Root (I.BVar n', s'_), s') as us'), vs'_) ->
          begin if n = n' then
            let (I.Dec (_, v'_)) = I.ctxDec g_ n in
            eqSpineR
              (gq, d_, ((s_, s), (v'_, I.id)), ((s'_, s'), (v'_, I.id)), sc, k)
          else k (gq, d_, [], Eq ((us_, vs_), (us', vs'_)), sc)
          end
      | gq, usVs, usVs' -> k (gq, d_, [], Eq (usVs, usVs'), sc)

    and eqSpineR (gq, d_, (ss_, vs_), (ss'_, vs'_), sc, k) =
      eqSpineRW (gq, d_, (ss_, Whnf.whnf vs_), (ss'_, Whnf.whnf vs'_), sc, k)

    and eqSpineRW (gq, d_, ssVs, ssVs', sc, k) = match ssVs, ssVs' with
      | ((Nil, s), vs_), ((Nil, s'), vs'_) -> true
      | ((I.SClo (s_, s'), s''), vs_), ssVs' ->
          eqSpineR (gq, d_, ((s_, I.comp s' s''), vs_), ssVs', sc, k)
      | ssVs, ((I.SClo (s'_, s'), s''), vs'_) ->
          eqSpineR (gq, d_, ssVs, ((s'_, I.comp s' s''), vs'_), sc, k)
      | ((I.App (u_, s_), s1), (I.Pi ((I.Dec (_, v1_), _), v2_), s2)), ((I.App (u'_, s'_), s1'), (I.Pi ((I.Dec (_, v1'), _), v2'), s2')) ->
          eqAtomicR
            (gq, d_, ((u_, s1), (v1_, s2)), ((u'_, s1'), (v1', s2')), sc, k)
          && eqSpineR
               ( gq,
                 d_,
                 ((s_, s1), (v2_, I.Dot (I.Exp (I.EClo (u_, s1)), s2))),
                 ((s'_, s1'), (v2', I.Dot (I.Exp (I.EClo (u'_, s1')), s2'))),
                 sc,
                 k )
      | ssVs, ssVs' -> false

    let rec leftDecompose (a, b, d'_, p_) = match a, b with
      | ((g_, q_) as gq), [] -> rightDecompose (gq, d'_, p_)
      | gq, Less (R.Arg usVs, R.Arg usVs') :: d_ ->
          ltAtomicL (gq, d_, d'_, usVs, usVs', p_)
      | gq, Less (R.Lex o_, R.Lex o'_) :: d_ ->
          ltLexL (gq, d_, d'_, o_, o'_, p_)
      | gq, Less (R.Simul o_, R.Simul o'_) :: d_ ->
          ltSimulL (gq, d_, d'_, o_, o'_, p_)
      | gq, Leq (R.Arg usVs, R.Arg usVs') :: d_ ->
          leAtomicL (gq, d_, d'_, usVs, usVs', p_)
      | gq, Leq (R.Lex o_, R.Lex o'_) :: d_ ->
          leftDecompose (gq, Less (R.Lex o_, R.Lex o'_) :: d_, d'_, p_)
          && leftDecompose (gq, Eq (R.Lex o_, R.Lex o'_) :: d_, d'_, p_)
      | gq, Leq (R.Simul o_, R.Simul o'_) :: d_ ->
          leSimulL (gq, d_, d'_, o_, o'_, p_)
      | gq, Eq (R.Arg usVs, R.Arg usVs') :: d_ ->
          eqAtomicL (gq, d_, d'_, usVs, usVs', p_)
      | gq, Eq (R.Lex o_, R.Lex o'_) :: d_ ->
          eqsL (gq, d_, d'_, o_, o'_, p_)
      | gq, Eq (R.Simul o_, R.Simul o'_) :: d_ ->
          eqsL (gq, d_, d'_, o_, o'_, p_)
      | ((g_, q_) as gq), Pi (dec_, o_) :: d_ -> begin
          begin if !Global.chatter > 3 then begin
            print " Ignoring quantified order ";
            print (F.makestring_fmt (fmtPredicate (g_, Pi (dec_, o_))))
          end
          else ()
          end;
          leftDecompose (gq, d_, d'_, p_)
        end

    and ltLexL (gq, d_, d'_, a, b, p_) = match a, b with
      | [], [] -> true
      | o_ :: l_, o'_ :: l'_ ->
          leftDecompose (gq, Less (o_, o'_) :: d_, d'_, p_)
          && ltLexL (gq, Eq (o_, o'_) :: d_, d'_, l_, l'_, p_)

    and eqsL (gq, d_, d'_, a, b, p_) = match a, b with
      | [], [] -> true
      | o_ :: l_, o'_ :: l'_ ->
          leftDecompose (gq, Eq (o_, o'_) :: d_, d'_, p_)
          && eqsL (gq, d_, d'_, l_, l'_, p_)

    and ltSimulL (gq, d_, d'_, a, b, p_) = match a, b with
      | [], [] -> leftDecompose (gq, d_, d'_, p_)
      | o_ :: l_, o'_ :: l'_ ->
          leSimulL (gq, Less (o_, o'_) :: d_, d'_, l_, l'_, p_)
          || ltSimulL (gq, Eq (o_, o'_) :: d_, d'_, l_, l'_, p_)

    and leSimulL (gq, d_, d'_, a, b, p_) = match a, b with
      | [], [] -> leftDecompose (gq, d_, d'_, p_)
      | o_ :: l_, o'_ :: l'_ ->
          leSimulL (gq, Leq (o_, o'_) :: d_, d'_, l_, l'_, p_)

    and ltAtomicL (gq, d_, d'_, usVs, usVs', p_) =
      ltAtomicLW (gq, d_, d'_, usVs, (let a__, b__ = usVs' in Whnf.whnfEta a__ b__), p_)

    and ltAtomicLW (a, d_, d'_, b, c, p_) = match a, b, c with
      | ((g_, q_) as gq), usVs, (us', ((I.Root _, s') as vs'_)) ->
          ltL (gq, d_, d'_, usVs, (us', vs'_), p_)
      | ((g_, q_) as gq), ((u_, s1), (v_, s2)), ((I.Lam (_, u'_), s1'), (I.Pi ((dec', _), v'_), s2')) ->
          let d1_ = shiftRCtx d_ (function s -> I.comp s I.shift) in
          let d1' = shiftACtx d'_ (function s -> I.comp s I.shift) in
          let usVs = ((u_, I.comp s1 I.shift), (v_, I.comp s2 I.shift)) in
          let usVs' = ((u'_, I.dot1 s1'), (v'_, I.dot1 s2')) in
          let p'_ = shiftP p_ (function s -> I.comp s I.shift) in
          ltAtomicL
            ( ( I.Decl (g_, N.decLUName g_ (I.decSub dec' s2')),
                I.Decl (q_, All) ),
              d1_,
              d1',
              usVs,
              usVs',
              p'_ )

    and leAtomicL (gq, d_, d'_, usVs, usVs', p_) =
      leAtomicLW (gq, d_, d'_, usVs, (let a__, b__ = usVs' in Whnf.whnfEta a__ b__), p_)

    and leAtomicLW (a, d_, d'_, b, c, p_) = match a, b, c with
      | gq, usVs, (us', ((I.Root (h_, s_), s') as vs'_)) ->
          leL (gq, d_, d'_, usVs, (us', vs'_), p_)
      | ((g_, q_) as gq), ((u_, s1), (v_, s2)), ((I.Lam (_, u'_), s1'), (I.Pi ((dec', _), v'_), s2')) ->
          let d1_ = shiftRCtx d_ (function s -> I.comp s I.shift) in
          let d1' = shiftACtx d'_ (function s -> I.comp s I.shift) in
          let usVs = ((u_, I.comp s1 I.shift), (v_, I.comp s2 I.shift)) in
          let usVs' = ((u'_, I.dot1 s1'), (v'_, I.dot1 s2')) in
          let p'_ = shiftP p_ (function s -> I.comp s I.shift) in
          leAtomicL
            ( ( I.Decl (g_, N.decLUName g_ (I.decSub dec' s2')),
                I.Decl (q_, All) ),
              d1_,
              d1',
              usVs,
              usVs',
              p'_ )

    and eqAtomicL (gq, d_, d'_, usVs, usVs', p_) =
      eqAtomicLW (gq, d_, d'_, (let a__, b__ = usVs in Whnf.whnfEta a__ b__), (let a__, b__ = usVs' in Whnf.whnfEta a__ b__), p_)

    and eqAtomicLW (gq, d_, d'_, a, b, p_) = match a, b with
      | (us_, ((I.Root _, s) as vs_)), (us', ((I.Root _, s') as vs'_)) ->
          eqL (gq, d_, d'_, (us_, vs_), (us', vs'_), p_)
      | (us_, ((I.Root _, s) as vs_)), (us', ((I.Pi _, s') as vs'_)) ->
          true
      | (us_, ((I.Pi _, s) as vs_)), (us', ((I.Root _, s') as vs'_)) ->
          true
      | (us_, ((I.Pi _, s) as vs_)), (us', ((I.Pi _, s') as vs'_)) ->
          leftDecompose (gq, d_, Eq ((us_, vs_), (us', vs'_)) :: d'_, p_)

    and leL (gq, d_, d'_, usVs, usVs', p_) =
      ltAtomicL (gq, d_, d'_, usVs, usVs', p_)
      && eqAtomicL (gq, d_, d'_, usVs, usVs', p_)

    and ltL (gq, d_, d'_, usVs, (us', vs'_), p_) =
      ltLW (gq, d_, d'_, usVs, (Whnf.whnf us', vs'_), p_)

    and ltLW (a, d_, d'_, usVs, b, p_) = match a, b with
      | ((g_, q_) as gq), (((I.Root (I.BVar n, s'_), s') as us'), vs'_) ->
          begin if isAtomic (gq, us') then
            leftDecompose (gq, d_, Less (usVs, (us', vs'_)) :: d'_, p_)
          else
            let (I.Dec (_, v'_)) = I.ctxDec g_ n in
            ltSpineL (gq, d_, d'_, usVs, ((s'_, s'), (v'_, I.id)), p_)
          end
      | gq, ((I.Root (I.Const c, s'_), s'), vs'_) ->
          ltSpineL (gq, d_, d'_, usVs, ((s'_, s'), (I.constType c, I.id)), p_)
      | gq, ((I.Root (I.Def c, s'_), s'), vs'_) ->
          ltSpineL (gq, d_, d'_, usVs, ((s'_, s'), (I.constType c, I.id)), p_)

    and ltSpineL (gq, d_, d'_, usVs, (ss'_, vs'_), p_) =
      ltSpineLW (gq, d_, d'_, usVs, (ss'_, Whnf.whnf vs'_), p_)

    and ltSpineLW = function
      | gq, d_, d'_, usVs, ((I.Nil, _), _), _ -> true
      | gq, d_, d'_, usVs, ((I.SClo (s_, s'), s''), vs'_), p_ ->
          ltSpineL (gq, d_, d'_, usVs, ((s_, I.comp s' s''), vs'_), p_)
      | ( gq,
          d_,
          d'_,
          usVs,
          ((I.App (u'_, s'_), s1'), (I.Pi ((I.Dec (_, v1'), _), v2'), s2')),
          p_ ) ->
          leAtomicL (gq, d_, d'_, usVs, ((u'_, s1'), (v1', s2')), p_)
          && ltSpineL
               ( gq,
                 d_,
                 d'_,
                 usVs,
                 ((s'_, s1'), (v2', I.Dot (I.Exp (I.EClo (u'_, s1')), s2'))),
                 p_ )

    and eqL (gq, d_, d'_, usVs, usVs', p_) =
      eqLW (gq, d_, d'_, (let a__, b__ = usVs in Whnf.whnfEta a__ b__), (let a__, b__ = usVs' in Whnf.whnfEta a__ b__), p_)

    and eqLW (a, d_, d'_, b, d, p_) = match a, b, d with
      | gq, (us_, ((I.Pi ((I.Dec (_, v2'), _), v'_), s2') as vs_)), (us', ((I.Pi ((I.Dec (_, v2''), _), v''), s2'') as vs'_)) ->
          leftDecompose (gq, d_, Eq ((us_, vs_), (us', vs'_)) :: d'_, p_)
      | gq, (us_, ((I.Pi ((I.Dec (_, v2'), _), v'_), s2') as vs_)), (us', ((I.Root _, s2'') as vs'_)) ->
          true
      | gq, (us_, ((I.Root _, s2') as vs_)), (us', ((I.Pi ((I.Dec (_, v2''), _), v''), s2'') as vs'_)) ->
          true
      | gq, (((I.Root (I.Const c, s_), s), vs_) as usVs), (((I.Root (I.Const c', s'_), s'), vs'_) as usVs') ->
          begin if eqCid (c, c') then
            eqSpineL
              ( gq,
                d_,
                d'_,
                ((s_, s), (I.constType c, I.id)),
                ((s'_, s'), (I.constType c', I.id)),
                p_ )
          else true
          end
      | gq, (((I.Root (I.Const c, s_), s) as us_), vs_), (((I.Root (I.BVar n, s'_), s') as us'), vs'_) ->
          begin if isAtomic (gq, us') then
            leftDecompose (gq, d_, Eq ((us', vs'_), (us_, vs_)) :: d'_, p_)
          else true
          end
      | gq, (((I.Root (I.BVar n, s_), s) as us_), vs_), (((I.Root (I.Const c, s'_), s') as us'), vs'_) ->
          begin if isAtomic (gq, us_) then
            leftDecompose (gq, d_, Eq ((us_, vs_), (us', vs'_)) :: d'_, p_)
          else true
          end
      | gq, (((I.Root (I.Def c, s_), s), vs_) as usVs), (((I.Root (I.Def c', s'_), s'), vs'_) as usVs') ->
          begin if eqCid (c, c') then
            eqSpineL
              ( gq,
                d_,
                d'_,
                ((s_, s), (I.constType c, I.id)),
                ((s'_, s'), (I.constType c', I.id)),
                p_ )
          else true
          end
      | gq, (((I.Root (I.Def c, s_), s) as us_), vs_), (((I.Root (I.BVar n, s'_), s') as us'), vs'_) ->
          begin if isAtomic (gq, us') then
            leftDecompose (gq, d_, Eq ((us', vs'_), (us_, vs_)) :: d'_, p_)
          else true
          end
      | gq, (((I.Root (I.BVar n, s_), s) as us_), vs_), (((I.Root (I.Def c, s'_), s') as us'), vs'_) ->
          begin if isAtomic (gq, us_) then
            leftDecompose (gq, d_, Eq ((us_, vs_), (us', vs'_)) :: d'_, p_)
          else true
          end
      | ((g_, q_) as gq), (((I.Root (I.BVar n, s_), s) as us_), vs_), (((I.Root (I.BVar n', s'_), s') as us'), vs'_) ->
          begin if n = n' then
            let (I.Dec (_, v'_)) = I.ctxDec g_ n in
            eqSpineL
              (gq, d_, d'_, ((s_, s), (v'_, I.id)), ((s'_, s'), (v'_, I.id)), p_)
          else leftDecompose (gq, d_, Eq ((us_, vs_), (us', vs'_)) :: d'_, p_)
          end
      | gq, usVs, usVs' ->
          leftDecompose (gq, d_, Eq (usVs, usVs') :: d'_, p_)

    and eqSpineL (gq, d_, d'_, (ss_, vs_), (ss'_, vs'_), p_) =
      eqSpineLW (gq, d_, d'_, (ss_, Whnf.whnf vs_), (ss'_, Whnf.whnf vs'_), p_)

    and eqSpineLW (gq, d_, d'_, ssVs, ssVs', p_) = match ssVs, ssVs' with
      | ((Nil, s), vs_), ((Nil, s'), vs'_) ->
          leftDecompose (gq, d_, d'_, p_)
      | ((I.SClo (s_, s'), s''), vs_), ssVs' ->
          eqSpineL (gq, d_, d'_, ((s_, I.comp s' s''), vs_), ssVs', p_)
      | ssVs, ((I.SClo (s'_, s'), s''), vs'_) ->
          eqSpineL (gq, d_, d'_, ssVs, ((s'_, I.comp s' s''), vs'_), p_)
      | ((I.App (u_, s_), s1), (I.Pi ((I.Dec (_, v1_), _), v2_), s2)), ((I.App (u'_, s'_), s1'), (I.Pi ((I.Dec (_, v1'), _), v2'), s2')) ->
          let d1_ =
            Eq (R.Arg ((u_, s1), (v1_, s2)), R.Arg ((u'_, s1'), (v1', s2')))
            :: d_
          in
          eqSpineL
            ( gq,
              d1_,
              d'_,
              ((s_, s1), (v2_, I.Dot (I.Exp (I.EClo (u_, s1)), s2))),
              ((s'_, s1'), (v2', I.Dot (I.Exp (I.EClo (u'_, s1')), s2'))),
              p_ )

    let deduce (g_, q_, d_, p_) = leftDecompose ((g_, q_), d_, [], p_)
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
(*! structure CsManager : CS_MANAGER !*)
(*! sharing CsManager.IntSyn = IntSyn' !*)
(* local *)
(* functor checking  *)

(* # 1 "src/terminate/Checking.sml.ml" *)
