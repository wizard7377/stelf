open! Global.Global_
open! Intsyn.Lambda_
open! Names.Names_
open! Print.Print_
open! Formatter__Formatter_
open! Index.Index_
open! Paths
open! Paths.Paths_
open! Solvers.Solvers_

(* # 1 "src/terminate/Checking.sig.ml" *)

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

    let atomicPredToString (g, a) = match a with
      | Less ((us, _), (us', _)) ->
          (Print.expToString g (mkEClo us) ^ " < ")
          ^ Print.expToString g (mkEClo us')
      | Leq ((us, _), (us', _)) ->
          (Print.expToString g (mkEClo us) ^ " <= ")
          ^ Print.expToString g (mkEClo us')
      | Eq ((us, _), (us', _)) ->
          (Print.expToString g (mkEClo us) ^ " = ")
          ^ Print.expToString g (mkEClo us')

    let rec atomicRCtxToString (g, a) = match a with
      | [] -> " "
      | o :: [] -> atomicPredToString (g, o)
      | o :: d' ->
          (atomicRCtxToString (g, d') ^ ", ") ^ atomicPredToString (g, o)

    let rec shiftO arg__1 arg__2 =
      begin match (arg__1, arg__2) with
      | R.Arg ((u, us), (v, vs)), f -> R.Arg ((u, f us), (v, f vs))
      | R.Lex l, f -> R.Lex (map (function o -> shiftO o f) l)
      | R.Simul l, f -> R.Simul (map (function o -> shiftO o f) l)
      end

    let rec shiftP arg__3 arg__4 =
      begin match (arg__3, arg__4) with
      | Less (o1, o2), f -> Less (shiftO o1 f, shiftO o2 f)
      | Leq (o1, o2), f -> Leq (shiftO o1 f, shiftO o2 f)
      | Eq (o1, o2), f -> Eq (shiftO o1 f, shiftO o2 f)
      | Pi ((I.Dec (x, v) as d), p), f -> Pi (d, shiftP p f)
      end

    let shiftRCtx rl f = map (function p -> shiftP p f) rl

    let shiftArg arg__5 arg__6 =
      begin match (arg__5, arg__6) with
      | Less (((u1, s1), (v1, s1')), ((u2, s2), (v2, s2'))), f ->
          Less (((u1, f s1), (v1, f s1')), ((u2, f s2), (v2, f s2')))
      | Leq (((u1, s1), (v1, s1')), ((u2, s2), (v2, s2'))), f ->
          Leq (((u1, f s1), (v1, f s1')), ((u2, f s2), (v2, f s2')))
      | Eq (((u1, s1), (v1, s1')), ((u2, s2), (v2, s2'))), f ->
          Eq (((u1, f s1), (v1, f s1')), ((u2, f s2), (v2, f s2')))
      end

    let shiftACtx rl f = map (function p -> shiftArg p f) rl

    let fmtOrder (g, o) =
      let rec fmtOrder' = function
        | R.Arg (((u, s) as us), ((v, s') as vs)) ->
            F.hbox
              [ F.string "("; Print.formatExp g (mkEClo us); F.string ")" ]
        | R.Lex l ->
            F.hbox
              [ F.string "{"; F.hOVbox0 1 0 1 (fmtOrders l); F.string "}" ]
        | R.Simul l ->
            F.hbox
              [ F.string "["; F.hOVbox0 1 0 1 (fmtOrders l); F.string "]" ]
      and fmtOrders = function
        | [] -> []
        | o :: [] -> [ fmtOrder' o ]
        | o :: l -> fmtOrder' o :: F.break :: fmtOrders l
      in
      fmtOrder' o

    let fmtComparison (g, o, comp, o') =
      F.hOVbox0 1 0 1
        [
          fmtOrder (g, o); F.break; F.string comp; F.break; fmtOrder (g, o');
        ]

    let rec fmtPredicate' (g, a) = match a with
      | Less (o, o') -> fmtComparison (g, o, "<", o')
      | Leq (o, o') -> fmtComparison (g, o, "<=", o')
      | Eq (o, o') -> fmtComparison (g, o, "=", o')
      | Pi (d, p) ->
          F.hbox [ F.string "Pi "; fmtPredicate' (I.Decl (g, d), p) ]

    let fmtPredicate (g, p) = fmtPredicate' (Names.ctxName g, p)

    let rec fmtRGCtx' (g, a) = match a with
      | [] -> ""
      | p :: [] -> F.makestring_fmt (fmtPredicate' (g, p))
      | p :: rl ->
          (F.makestring_fmt (fmtPredicate' (g, p)) ^ " ,")
          ^ fmtRGCtx' (g, rl)

    let fmtRGCtx (g, rl) = fmtRGCtx' (Names.ctxName g, rl)
    let init () = true
    let eqCid (c, c') = c = c'

    let conv (us, vs) (us', vs') =
      Conv.conv vs vs' && Conv.conv us us'

    let isUniversal = function All -> true | Exist -> false | exist' -> false
    let isExistential = function All -> false | Exist -> true | exist' -> true

    let rec isParameter (q, x) = isParameterW (q, Whnf.whnf (x, I.id))

    and isParameterW (q, us) =
      try isUniversal (I.ctxLookup q (Whnf.etaContract (mkEClo us)))
      with Whnf.Eta -> isFreeEVar us

    and isFreeEVar = function
      | I.EVar (_, _, _, { contents = [] }), _ -> true
      | I.Lam (d, u), s -> isFreeEVar (Whnf.whnf (u, I.dot1 s))
      | _ -> false

    let rec isAtomic (gq, us) = isAtomicW (gq, Whnf.whnf us)

    and isAtomicW = function
      | gq, ((I.Root (I.Const c, s_) as x), s) -> isAtomicS (gq, (s_, s))
      | gq, ((I.Root (I.Def c, s_) as x), s) -> isAtomicS (gq, (s_, s))
      | ((g, q) as gq), ((I.Root (I.BVar n, s_) as x), s) ->
          isExistential (I.ctxLookup q n) || isAtomicS (gq, (s_, s))
      | gq, _ -> false

    and isAtomicS (gq, a) = match a with
      | (I.Nil, _) -> true
      | (I.SClo (s, s'), s'') -> isAtomicS (gq, (s, I.comp s' s''))
      | (I.App (u', s'), s1') -> false

    let eq (g, (us, vs), (us', vs')) =
      Unify.unifiable g vs vs' && Unify.unifiable g us us'

    let rec lookupEq (a, b, usVs, usVs', sc) = match a, b with
      | gq, [] -> false
      | gq, Less (_, _) :: d ->
          lookupEq (gq, d, usVs, usVs', sc)
      | ((g, q) as gq), Eq (usVs1, usVs1') :: d ->
          CsManager.trail (function () ->
              eq (g, usVs1, usVs) && eq (g, usVs1', usVs') && sc ())
          || CsManager.trail (function () ->
              eq (g, usVs1, usVs') && eq (g, usVs1', usVs) && sc ())
          || lookupEq (gq, d, usVs, usVs', sc)

    let rec lookupLt (a, b, usVs, usVs', sc) = match a, b with
      | gq, [] -> false
      | gq, Eq (_, _) :: d ->
          lookupLt (gq, d, usVs, usVs', sc)
      | ((g, q) as gq), Less (usVs1, usVs1') :: d ->
          CsManager.trail (function () ->
              eq (g, usVs1, usVs) && eq (g, usVs1', usVs') && sc ())
          || lookupLt (gq, d, usVs, usVs', sc)

    let rec eqAtomic (a, d, d', usVs, usVs', sc) = match a, d with
      | ((g, q) as gq), [] ->
          CsManager.trail (function () -> eq (g, usVs, usVs') && sc ())
          || lookupEq (gq, d', usVs, usVs', sc)
      | ((g, q) as gq), d ->
          CsManager.trail (function () -> eq (g, usVs, usVs') && sc ())
          || lookupEq (gq, d, usVs, usVs', sc)
          || lookupEq (gq, d', usVs, usVs', sc)
          || transEq (gq, d, d', usVs, usVs', sc)

    and transEq (a, b, d', usVs, usVs', sc) = match a, b, d' with
      | ((g, q) as gq), [], d -> false
      | ((g, q) as gq), Eq (usVs1, usVs1') :: d, d' ->
          CsManager.trail (function () ->
              eq (g, usVs1', usVs')
              && sc ()
              && eqAtomicR (gq, d @ d', usVs, usVs1, sc, atomic))
          || CsManager.trail (function () ->
              eq (g, usVs1, usVs')
              && sc ()
              && eqAtomicR (gq, d @ d', usVs, usVs1', sc, atomic))
          || transEq (gq, d, Eq (usVs1, usVs1') :: d', usVs, usVs', sc)
      | ((g, q) as gq), Less (usVs1, usVs1') :: d, d' ->
          transEq (gq, d, d', usVs, usVs', sc)

    and ltAtomic (a, d, d', usVs, usVs', sc) = match a, d with
      | ((g, q) as gq), [] ->
          lookupLt (gq, d', usVs, usVs', sc)
      | ((g, q) as gq), d ->
          lookupLt (gq, d, usVs, usVs', sc)
          || lookupLt (gq, d', usVs, usVs', sc)
          || transLt (gq, d, d', usVs, usVs', sc)

    and transLt (a, b, d', usVs, usVs', sc) = match a, b, d' with
      | ((g, q) as gq), [], d -> false
      | ((g, q) as gq), Eq (usVs1, usVs1') :: d, d' ->
          CsManager.trail (function () ->
              eq (g, usVs1', usVs')
              && sc ()
              && ltAtomicR (gq, d @ d', usVs, usVs1, sc, atomic))
          || CsManager.trail (function () ->
              eq (g, usVs1, usVs')
              && sc ()
              && ltAtomicR (gq, d @ d', usVs, usVs1', sc, atomic))
          || transLt (gq, d, Eq (usVs1, usVs1') :: d', usVs, usVs', sc)
      | ((g, q) as gq), Less (usVs1, usVs1') :: d, d' ->
          CsManager.trail (function () ->
              eq (g, usVs1', usVs')
              && sc ()
              && eqAtomicR (gq, d @ d', usVs, usVs1, sc, atomic))
          || CsManager.trail (function () ->
              eq (g, usVs1', usVs')
              && sc ()
              && ltAtomicR (gq, d @ d', usVs, usVs1, sc, atomic))
          || transLt (gq, d, Less (usVs1, usVs1') :: d', usVs, usVs', sc)

    and atomic (gq, d, d', a, sc) = match a with
      | Eq (usVs, usVs') ->
          eqAtomic (gq, d, d', usVs, usVs', sc)
      | Less (usVs, usVs') ->
          ltAtomic (gq, d, d', usVs, usVs', sc)

    and leftInstantiate (a, b, d', p, sc) = match a, b with
      | ((g, q) as gq), [] ->
          begin if atomic (gq, d', [], p, sc) then begin
            begin if !Global.chatter > 4 then
              print
                ((((" Proved: " ^ atomicRCtxToString (g, d')) ^ " ---> ")
                 ^ atomicPredToString (g, p))
                ^ "\n")
            else ()
            end;
            true
          end
          else false
          end
      | gq, Less (usVs, usVs') :: d ->
          ltInstL (gq, d, d', usVs, usVs', p, sc)
      | gq, Leq (usVs, usVs') :: d ->
          leInstL (gq, d, d', usVs, usVs', p, sc)
      | gq, Eq (usVs, usVs') :: d ->
          eqInstL (gq, d, d', usVs, usVs', p, sc)

    and ltInstL (gq, d, d', usVs, usVs', p', sc) =
      ltInstLW (gq, d, d', (let a__, b__ = usVs in Whnf.whnfEta a__ b__), usVs', p', sc)

    and ltInstLW (a, d, d', usVs, usVs', p', sc) = match a, usVs, usVs' with
      | ((g, q) as gq), ( (I.Lam ((I.Dec (_, v1) as dec), u), s1),
            (I.Pi ((I.Dec (_, v2), _), v), s2) ), ((u', s1'), (v', s2')) ->
          begin if Subordinate.equiv (I.targetFam v') (I.targetFam v1) then
            let x = I.newEVar g (I.EClo (v1, s1)) in
            let sc' () = isParameter (q, x) && sc () in
            ltInstL
              ( (g, q),
                d,
                d',
                ((u, I.Dot (I.Exp x, s1)), (v, I.Dot (I.Exp x, s2))),
                ((u', s1'), (v', s2')),
                p',
                sc' )
          else
            begin if Subordinate.below (I.targetFam v1) (I.targetFam v') then
              let x = I.newEVar g (I.EClo (v1, s1)) in
              ltInstL
                ( (g, q),
                  d,
                  d',
                  ((u, I.Dot (I.Exp x, s1)), (v, I.Dot (I.Exp x, s2))),
                  ((u', s1'), (v', s2')),
                  p',
                  sc )
            else false
            end
          end
      | gq, usVs, usVs' ->
          leftInstantiate (gq, d, Less (usVs, usVs') :: d', p', sc)

    and leInstL (gq, d, d', usVs, usVs', p', sc) =
      leInstLW (gq, d, d', (let a__, b__ = usVs in Whnf.whnfEta a__ b__), usVs', p', sc)

    and leInstLW (a, d, d', usVs, usVs', p', sc) = match a, usVs, usVs', p' with
      | ((g, q) as gq), ( (I.Lam (I.Dec (_, v1), u), s1),
            (I.Pi ((I.Dec (_, v2), _), v), s2) ), ((u', s1'), (v', s2')), p' ->
          begin if Subordinate.equiv (I.targetFam v') (I.targetFam v1) then
            let x = I.newEVar g (I.EClo (v1, s1)) in
            let sc' () = isParameter (q, x) && sc () in
            leInstL
              ( (g, q),
                d,
                d',
                ((u, I.Dot (I.Exp x, s1)), (v, I.Dot (I.Exp x, s2))),
                ((u', s1'), (v', s2')),
                p',
                sc' )
          else
            begin if Subordinate.below (I.targetFam v1) (I.targetFam v') then
              let x = I.newEVar g (I.EClo (v1, s1)) in
              leInstL
                ( (g, q),
                  d,
                  d',
                  ((u, I.Dot (I.Exp x, s1)), (v, I.Dot (I.Exp x, s2))),
                  ((u', s1'), (v', s2')),
                  p',
                  sc )
            else false
            end
          end
      | gq, usVs, usVs', p ->
          leftInstantiate (gq, d, Less (usVs, usVs') :: d', p, sc)

    and eqInstL (gq, d, d', usVs, usVs', p', sc) =
      eqInstLW (gq, d, d', (let a__, b__ = usVs in Whnf.whnfEta a__ b__), (let a__, b__ = usVs' in Whnf.whnfEta a__ b__), p', sc)

    and eqInstLW (a, d, d', usVs, usVs', p', sc) = match a, usVs, usVs' with
      | ((g, q) as gq), ( (I.Lam (I.Dec (_, v1'), u'), s1'),
            (I.Pi ((I.Dec (_, v2'), _), v'), s2') ), ( (I.Lam (I.Dec (_, v1''), u''), s1''),
            (I.Pi ((I.Dec (_, v2''), _), v''), s2'') ) ->
          let x = I.newEVar g (I.EClo (v1'', s1'')) in
          eqInstL
            ( gq,
              d,
              d',
              ((u', I.Dot (I.Exp x, s1')), (v', I.Dot (I.Exp x, s2'))),
              ((u'', I.Dot (I.Exp x, s1'')), (v'', I.Dot (I.Exp x, s2''))),
              p',
              function
              | () -> begin
                  ignore (isParameter (q, x));
                  sc ()
                end )
      | gq, usVs, usVs' ->
          eqIL (gq, d, d', usVs, usVs', p', sc)

    and eqIL (a, d_, d', b, d, p', sc) = match a, b, d with
      | ((g, q) as gq), (((I.Root (I.Const c, s_), s), vs) as usVs), (((I.Root (I.Const c', s'_), s'), vs') as usVs') ->
          begin if eqCid (c, c') then
            eqSpineIL
              ( gq,
                d_,
                d',
                ((s_, s), (I.constType c, I.id)),
                ((s'_, s'), (I.constType c', I.id)),
                p',
                sc )
          else begin
            begin if !Global.chatter > 4 then
              print
                (((((" Proved: "
                    ^ atomicRCtxToString (g, Eq (usVs, usVs') :: d_))
                   ^ atomicRCtxToString (g, d'))
                  ^ " ---> ")
                 ^ atomicPredToString (g, p'))
                ^ "\n")
            else ()
            end;
            true
          end
          end
      | ((g, q) as gq), (((I.Root (I.Def c, s_), s), vs) as usVs), (((I.Root (I.Def c', s'_), s'), vs') as usVs') ->
          begin if eqCid (c, c') then
            eqSpineIL
              ( gq,
                d_,
                d',
                ((s_, s), (I.constType c, I.id)),
                ((s'_, s'), (I.constType c', I.id)),
                p',
                sc )
          else begin
            begin if !Global.chatter > 4 then
              print
                (((((" Proved: "
                    ^ atomicRCtxToString (g, Eq (usVs, usVs') :: d_))
                   ^ atomicRCtxToString (g, d'))
                  ^ " ---> ")
                 ^ atomicPredToString (g, p'))
                ^ "\n")
            else ()
            end;
            true
          end
          end
      | ((g, q) as gq), (((I.Root (I.Const c, s_), s) as us), vs), (((I.Root (I.BVar n, s'_), s') as us'), vs') ->
          begin if isAtomic (gq, us') then
            leftInstantiate
              (gq, d_, Eq ((us', vs'), (us, vs)) :: d', p', sc)
          else begin
            begin if !Global.chatter > 4 then
              print
                (((((" Proved: "
                    ^ atomicRCtxToString (g, Eq ((us, vs), (us', vs')) :: d_)
                    )
                   ^ atomicRCtxToString (g, d'))
                  ^ " ---> ")
                 ^ atomicPredToString (g, p'))
                ^ "\n")
            else ()
            end;
            true
          end
          end
      | ((g, q) as gq), (((I.Root (I.Def c, s_), s) as us), vs), (((I.Root (I.BVar n, s'_), s') as us'), vs') ->
          begin if isAtomic (gq, us') then
            leftInstantiate
              (gq, d_, Eq ((us', vs'), (us, vs)) :: d', p', sc)
          else begin
            begin if !Global.chatter > 4 then
              print
                (((((" Proved: "
                    ^ atomicRCtxToString (g, Eq ((us, vs), (us', vs')) :: d_)
                    )
                   ^ atomicRCtxToString (g, d'))
                  ^ " ---> ")
                 ^ atomicPredToString (g, p'))
                ^ "\n")
            else ()
            end;
            true
          end
          end
      | ((g, q) as gq), (((I.Root (I.BVar n, s_), s) as us), vs), (((I.Root (I.Def c, s'_), s') as us'), vs') ->
          begin if isAtomic (gq, us) then
            leftInstantiate
              (gq, d_, Eq ((us, vs), (us', vs')) :: d', p', sc)
          else begin
            begin if !Global.chatter > 4 then
              print
                (((((" Proved: "
                    ^ atomicRCtxToString
                        (g, Eq ((us, vs), (us', vs')) :: d'))
                   ^ atomicRCtxToString (g, d'))
                  ^ " ---> ")
                 ^ atomicPredToString (g, p'))
                ^ "\n")
            else ()
            end;
            true
          end
          end
      | ((g, q) as gq), (((I.Root (I.BVar n, s_), s) as us), vs), (((I.Root (I.Const c, s'_), s') as us'), vs') ->
          begin if isAtomic (gq, us) then
            leftInstantiate
              (gq, d_, Eq ((us, vs), (us', vs')) :: d', p', sc)
          else begin
            begin if !Global.chatter > 4 then
              print
                (((((" Proved: "
                    ^ atomicRCtxToString
                        (g, Eq ((us, vs), (us', vs')) :: d'))
                   ^ atomicRCtxToString (g, d'))
                  ^ " ---> ")
                 ^ atomicPredToString (g, p'))
                ^ "\n")
            else ()
            end;
            true
          end
          end
      | ((g, q) as gq), (((I.Root (I.BVar n, s_), s) as us), vs), (((I.Root (I.BVar n', s'_), s') as us'), vs') ->
          begin if n = n' then
            let (I.Dec (_, v')) = I.ctxDec g n in
            eqSpineIL
              ( gq,
                d_,
                d',
                ((s_, s), (v', I.id)),
                ((s'_, s'), (v', I.id)),
                p',
                sc )
          else
            leftInstantiate
              (gq, d_, Eq ((us, vs), (us', vs')) :: d', p', sc)
          end
      | ((g, q) as gq), usVs, usVs' -> begin
          begin if !Global.chatter > 4 then
            print
              (((((" Proved: " ^ atomicRCtxToString (g, Eq (usVs, usVs') :: d_))
                 ^ atomicRCtxToString (g, d'))
                ^ " ---> ")
               ^ atomicPredToString (g, p'))
              ^ "\n")
          else ()
          end;
          true
        end

    and eqSpineIL (gq, d, d', (ss, vs), (ss', vs'), p', sc) =
      eqSpineILW
        (gq, d, d', (ss, Whnf.whnf vs), (ss', Whnf.whnf vs'), p', sc)

    and eqSpineILW (gq, d, d', ssVs, ssVs', p', sc) = match ssVs, ssVs' with
      | ((Nil, s), vs), ((Nil, s'), vs') ->
          leftInstantiate (gq, d, d', p', sc)
      | ((I.SClo (s, s'), s''), vs), ssVs' ->
          eqSpineIL (gq, d, d', ((s, I.comp s' s''), vs), ssVs', p', sc)
      | ssVs, ((I.SClo (s'_, s'), s''), vs') ->
          eqSpineIL (gq, d, d', ssVs, ((s'_, I.comp s' s''), vs'), p', sc)
      | ((I.App (u, s), s1), (I.Pi ((I.Dec (_, v1), _), v2), s2)), ((I.App (u', s'), s1'), (I.Pi ((I.Dec (_, v1'), _), v2'), s2')) ->
          let d1 =
            Eq (((u, s1), (v1, s2)), ((u', s1'), (v1', s2'))) :: d
          in
          eqSpineIL
            ( gq,
              d1,
              d',
              ((s, s1), (v2, I.Dot (I.Exp (I.EClo (u, s1)), s2))),
              ((s', s1'), (v2', I.Dot (I.Exp (I.EClo (u', s1')), s2'))),
              p',
              sc )

    and rightDecompose (gq, d', a) = match a with
      | Less (o, o') -> ordLtR (gq, d', o, o')
      | Leq (o, o') -> ordLeR (gq, d', o, o')
      | Eq (o, o') -> ordEqR (gq, d', o, o')

    and ordLtR (gq, d', a, b) = match a, b with
      | R.Arg usVs, R.Arg usVs' ->
          ltAtomicR (gq, d', usVs, usVs', init, leftInstantiate)
      | R.Lex o, R.Lex o' -> ltLexR (gq, d', o, o')
      | R.Simul o, R.Simul o' -> ltSimulR (gq, d', o, o')

    and ordLeR (gq, d', a, b) = match a, b with
      | R.Arg usVs, R.Arg usVs' ->
          leAtomicR (gq, d', usVs, usVs', init, leftInstantiate)
      | R.Lex o, R.Lex o' ->
          ltLexR (gq, d', o, o') || ordEqsR (gq, d', o, o')
      | R.Simul o, R.Simul o' -> leSimulR (gq, d', o, o')

    and ordEqR (gq, d', a, b) = match a, b with
      | R.Arg usVs, R.Arg usVs' ->
          conv usVs usVs'
          || eqAtomicR (gq, d', usVs, usVs', init, leftInstantiate)
      | R.Lex o, R.Lex o' -> ordEqsR (gq, d', o, o')
      | R.Simul o, R.Simul o' -> ordEqsR (gq, d', o, o')

    and ordEqsR (gq, d', a, b) = match a, b with
      | [], [] -> true
      | o :: l, o' :: l' ->
          ordEqR (gq, d', o, o') && ordEqsR (gq, d', l, l')

    and ltLexR (gq, d', a, b) = match a, b with
      | [], [] -> false
      | o :: l, o' :: l' ->
          ordLtR (gq, d', o, o')
          || (ordEqR (gq, d', o, o') && ltLexR (gq, d', l, l'))

    and leLexR (gq, d', l, l') =
      ltLexR (gq, d', l, l') || ordEqsR (gq, d', l, l')

    and ltSimulR (gq, d, a, b) = match a, b with
      | [], [] -> false
      | o :: l, o' :: l' ->
          (ordLtR (gq, d, o, o') && leSimulR (gq, d, l, l'))
          || (ordEqR (gq, d, o, o') && ltSimulR (gq, d, l, l'))

    and leSimulR (gq, d, a, b) = match a, b with
      | [], [] -> true
      | o :: l, o' :: l' ->
          ordLeR (gq, d, o, o') && leSimulR (gq, d, l, l')

    and ltAtomicR (gq, d, usVs, usVs', sc, k) =
      ltAtomicRW (gq, d, (let a__, b__ = usVs in Whnf.whnfEta a__ b__), usVs', sc, k)

    and ltAtomicRW (a, d, b, c, sc, k) = match a, b, c with
      | gq, ((us, ((I.Root _, s') as vs)) as usVs), usVs' ->
          ltR (gq, d, usVs, usVs', sc, k)
      | ((g, q) as gq), ((I.Lam (_, u), s1), (I.Pi ((dec, _), v), s2)), ((u', s1'), (v', s2')) ->
          let usVs' =
            ((u', I.comp s1' I.shift), (v', I.comp s2' I.shift))
          in
          let usVs = ((u, I.dot1 s1), (v, I.dot1 s2)) in
          let d' = shiftACtx d (function s -> I.comp s I.shift) in
          ltAtomicR
            ( ( I.Decl (g, N.decLUName g (I.decSub dec s2)),
                I.Decl (q, All) ),
              d',
              usVs,
              usVs',
              sc,
              k )

    and leAtomicR (gq, d, usVs, usVs', sc, k) =
      leAtomicRW (gq, d, (let a__, b__ = usVs in Whnf.whnfEta a__ b__), usVs', sc, k)

    and leAtomicRW (a, d, b, c, sc, k) = match a, b, c with
      | gq, ((us, ((I.Root _, s') as vs)) as usVs), usVs' ->
          leR (gq, d, usVs, usVs', sc, k)
      | ((g, q) as gq), ((I.Lam (_, u), s1), (I.Pi ((dec, _), v), s2)), ((u', s1'), (v', s2')) ->
          let d' = shiftACtx d (function s -> I.comp s I.shift) in
          let usVs' =
            ((u', I.comp s1' I.shift), (v', I.comp s2' I.shift))
          in
          let usVs = ((u, I.dot1 s1), (v, I.dot1 s2)) in
          leAtomicR
            ( ( I.Decl (g, N.decLUName g (I.decSub dec s2)),
                I.Decl (q, All) ),
              d',
              usVs,
              usVs',
              sc,
              k )

    and eqAtomicR (((g, q) as gq), d, usVs, usVs', sc, k) =
      eqAtomicRW (gq, d, (let a__, b__ = usVs in Whnf.whnfEta a__ b__), (let a__, b__ = usVs' in Whnf.whnfEta a__ b__), sc, k)

    and eqAtomicRW (a, d, b, c, sc, k) = match a, b, c with
      | ((g, q) as gq), ((I.Lam (_, u), s1), (I.Pi ((dec, _), v), s2)), ((I.Lam (_, u'), s1'), (I.Pi ((dec', _), v'), s2')) ->
          eqAtomicR
            ( ( I.Decl (g, N.decLUName g (I.decSub dec s2)),
                I.Decl (q, All) ),
              shiftACtx d (function s -> I.comp s I.shift),
              ((u, I.dot1 s1'), (v, I.dot1 s2')),
              ((u', I.dot1 s1'), (v', I.dot1 s2')),
              sc,
              k )
      | gq, (us, ((I.Root _, s2) as vs)), (us', ((I.Root _, s2') as vs')) ->
          eqR (gq, d, (us, vs), (us', vs'), sc, k)
      | gq, (us, vs), (us', vs') -> false

    and ltR (((g, q) as gq), d, usVs, usVs', sc, k) =
      ltRW (gq, d, usVs, (let a__, b__ = usVs' in Whnf.whnfEta a__ b__), sc, k)

    and ltRW (a, d_, b, d, sc, k) = match a, b, d with
      | gq, (us, vs), (((I.Root (I.Const c, s'_), s') as us'), vs') ->
          begin if isAtomic (gq, us') then
            k (gq, d_, [], Less ((us, vs), (us', vs')), sc)
          else
            ltSpineR
              (gq, d_, (us, vs), ((s'_, s'), (I.constType c, I.id)), sc, k)
          end
      | gq, (us, vs), (((I.Root (I.Def c, s'_), s') as us'), vs')
        ->
          begin if isAtomic (gq, us') then
            k (gq, d_, [], Less ((us, vs), (us', vs')), sc)
          else
            ltSpineR
              (gq, d_, (us, vs), ((s'_, s'), (I.constType c, I.id)), sc, k)
          end
      | ((g, q) as gq), (us, vs), (((I.Root (I.BVar n, s'_), s') as us'), vs') ->
          begin if isAtomic (gq, us') then
            k (gq, d_, [], Less ((us, vs), (us', vs')), sc)
          else
            let (I.Dec (_, v')) = I.ctxDec g n in
            ltSpineR (gq, d_, (us, vs), ((s'_, s'), (v', I.id)), sc, k)
          end
      | gq, _, ((I.EVar _, _), _) -> false
      | ((g, q) as gq), ((u, s1), (v, s2)), ( (I.Lam (I.Dec (_, v1'), u'), s1'),
            (I.Pi ((I.Dec (_, v2'), _), v'), s2') ) ->
          begin if Subordinate.equiv (I.targetFam v) (I.targetFam v1') then
            let x = I.newEVar g (I.EClo (v1', s1')) in
            let sc' = function
              | () -> begin
                  ignore (isParameter (q, x));
                  sc ()
                end
            in
            ltR
              ( gq,
                d_,
                ((u, s1), (v, s2)),
                ((u', I.Dot (I.Exp x, s1')), (v', I.Dot (I.Exp x, s2'))),
                sc',
                k )
          else
            begin if Subordinate.below (I.targetFam v1') (I.targetFam v) then
              let x = I.newEVar g (I.EClo (v1', s1')) in
              ltR
                ( gq,
                  d_,
                  ((u, s1), (v, s2)),
                  ((u', I.Dot (I.Exp x, s1')), (v', I.Dot (I.Exp x, s2'))),
                  sc,
                  k )
            else false
            end
          end

    and ltSpineR (gq, d, (us, vs), (ss', vs'), sc, k) =
      ltSpineRW (gq, d, (us, vs), (ss', Whnf.whnf vs'), sc, k)

    and ltSpineRW (gq, d, a, b, sc, k) = match a, b with
      | (us, vs), ((I.Nil, _), _) -> false
      | (us, vs), ((I.SClo (s, s'), s''), vs') ->
          ltSpineR (gq, d, (us, vs), ((s, I.comp s' s''), vs'), sc, k)
      | (us, vs), ((I.App (u', s'), s1'), (I.Pi ((I.Dec (_, v1'), _), v2'), s2')) ->
          leAtomicR (gq, d, (us, vs), ((u', s1'), (v1', s2')), sc, k)
          || ltSpineR
               ( gq,
                 d,
                 (us, vs),
                 ((s', s1'), (v2', I.Dot (I.Exp (I.EClo (u', s1')), s2'))),
                 sc,
                 k )

    and leR (gq, d, usVs, usVs', sc, k) =
      leRW (gq, d, usVs, (let a__, b__ = usVs' in Whnf.whnfEta a__ b__), sc, k)

    and leRW (a, d, usVs, usVs', sc, k) = match a, usVs, usVs' with
      | ((g, q) as gq), ((u, s1), (v, s2)), ( (I.Lam (I.Dec (_, v1'), u'), s1'),
            (I.Pi ((I.Dec (_, v2'), _), v'), s2') ) ->
          begin if Subordinate.equiv (I.targetFam v) (I.targetFam v1') then
            let x = I.newEVar g (I.EClo (v1', s1')) in
            let sc' () = isParameter (q, x) && sc () in
            leR
              ( gq,
                d,
                ((u, s1), (v, s2)),
                ((u', I.Dot (I.Exp x, s1')), (v', I.Dot (I.Exp x, s2'))),
                sc',
                k )
          else
            begin if Subordinate.below (I.targetFam v1') (I.targetFam v) then
              let x = I.newEVar g (I.EClo (v1', s1')) in
              leR
                ( gq,
                  d,
                  ((u, s1), (v, s2)),
                  ((u', I.Dot (I.Exp x, s1')), (v', I.Dot (I.Exp x, s2'))),
                  sc,
                  k )
            else false
            end
          end
      | gq, usVs, usVs' ->
          ltR (gq, d, usVs, usVs', sc, k) || eqR (gq, d, usVs, usVs', sc, k)

    and eqR (((g, q) as gq), d, usVs, usVs', sc, k) =
      CsManager.trail (function () -> eq (g, usVs, usVs') && sc ())
      || eqR' (gq, d, usVs, usVs', sc, k)

    and eqR' (a, d_, b, d, sc, k) = match a, b, d with
      | gq, (us, ((I.Pi ((I.Dec (_, v2'), _), v'), s2') as vs)), (us', ((I.Root _, s2'') as vs')) ->
          false
      | gq, (us, ((I.Root _, s2') as vs)), (us', ((I.Pi ((I.Dec (_, v2''), _), v''), s2'') as vs')) ->
          false
      | gq, (((I.Root (I.Const c, s_), s), vs) as usVs), (((I.Root (I.Const c', s'_), s'), vs') as usVs') ->
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
      | gq, (((I.Root (I.Const c, s_), s) as us), vs), (((I.Root (I.BVar n, s'_), s') as us'), vs') ->
          begin if isAtomic (gq, us') then
            k (gq, d_, [], Eq ((us', vs'), (us, vs)), sc)
          else false
          end
      | gq, (((I.Root (I.BVar n, s_), s) as us), vs), (((I.Root (I.Const c, s'_), s') as us'), vs') ->
          begin if isAtomic (gq, us) then
            k (gq, d_, [], Eq ((us, vs), (us', vs')), sc)
          else false
          end
      | gq, (((I.Root (I.Def c, s_), s), vs) as usVs), (((I.Root (I.Def c', s'_), s'), vs') as usVs') ->
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
      | gq, (((I.Root (I.Def c, s_), s) as us), vs), (((I.Root (I.BVar n, s'_), s') as us'), vs') ->
          begin if isAtomic (gq, us') then
            k (gq, d_, [], Eq ((us', vs'), (us, vs)), sc)
          else false
          end
      | gq, (((I.Root (I.BVar n, s_), s) as us), vs), (((I.Root (I.Def c, s'_), s') as us'), vs') ->
          begin if isAtomic (gq, us) then
            k (gq, d_, [], Eq ((us, vs), (us', vs')), sc)
          else false
          end
      | ((g, q) as gq), (((I.Root (I.BVar n, s_), s) as us), vs), (((I.Root (I.BVar n', s'_), s') as us'), vs') ->
          begin if n = n' then
            let (I.Dec (_, v')) = I.ctxDec g n in
            eqSpineR
              (gq, d_, ((s_, s), (v', I.id)), ((s'_, s'), (v', I.id)), sc, k)
          else k (gq, d_, [], Eq ((us, vs), (us', vs')), sc)
          end
      | gq, usVs, usVs' -> k (gq, d_, [], Eq (usVs, usVs'), sc)

    and eqSpineR (gq, d, (ss, vs), (ss', vs'), sc, k) =
      eqSpineRW (gq, d, (ss, Whnf.whnf vs), (ss', Whnf.whnf vs'), sc, k)

    and eqSpineRW (gq, d, ssVs, ssVs', sc, k) = match ssVs, ssVs' with
      | ((Nil, s), vs), ((Nil, s'), vs') -> true
      | ((I.SClo (s, s'), s''), vs), ssVs' ->
          eqSpineR (gq, d, ((s, I.comp s' s''), vs), ssVs', sc, k)
      | ssVs, ((I.SClo (s'_, s'), s''), vs') ->
          eqSpineR (gq, d, ssVs, ((s'_, I.comp s' s''), vs'), sc, k)
      | ((I.App (u, s), s1), (I.Pi ((I.Dec (_, v1), _), v2), s2)), ((I.App (u', s'), s1'), (I.Pi ((I.Dec (_, v1'), _), v2'), s2')) ->
          eqAtomicR
            (gq, d, ((u, s1), (v1, s2)), ((u', s1'), (v1', s2')), sc, k)
          && eqSpineR
               ( gq,
                 d,
                 ((s, s1), (v2, I.Dot (I.Exp (I.EClo (u, s1)), s2))),
                 ((s', s1'), (v2', I.Dot (I.Exp (I.EClo (u', s1')), s2'))),
                 sc,
                 k )
      | ssVs, ssVs' -> false

    let rec leftDecompose (a, b, d', p) = match a, b with
      | ((g, q) as gq), [] -> rightDecompose (gq, d', p)
      | gq, Less (R.Arg usVs, R.Arg usVs') :: d ->
          ltAtomicL (gq, d, d', usVs, usVs', p)
      | gq, Less (R.Lex o, R.Lex o') :: d ->
          ltLexL (gq, d, d', o, o', p)
      | gq, Less (R.Simul o, R.Simul o') :: d ->
          ltSimulL (gq, d, d', o, o', p)
      | gq, Leq (R.Arg usVs, R.Arg usVs') :: d ->
          leAtomicL (gq, d, d', usVs, usVs', p)
      | gq, Leq (R.Lex o, R.Lex o') :: d ->
          leftDecompose (gq, Less (R.Lex o, R.Lex o') :: d, d', p)
          && leftDecompose (gq, Eq (R.Lex o, R.Lex o') :: d, d', p)
      | gq, Leq (R.Simul o, R.Simul o') :: d ->
          leSimulL (gq, d, d', o, o', p)
      | gq, Eq (R.Arg usVs, R.Arg usVs') :: d ->
          eqAtomicL (gq, d, d', usVs, usVs', p)
      | gq, Eq (R.Lex o, R.Lex o') :: d ->
          eqsL (gq, d, d', o, o', p)
      | gq, Eq (R.Simul o, R.Simul o') :: d ->
          eqsL (gq, d, d', o, o', p)
      | ((g, q) as gq), Pi (dec, o) :: d -> begin
          begin if !Global.chatter > 3 then begin
            print " Ignoring quantified order ";
            print (F.makestring_fmt (fmtPredicate (g, Pi (dec, o))))
          end
          else ()
          end;
          leftDecompose (gq, d, d', p)
        end

    and ltLexL (gq, d, d', a, b, p) = match a, b with
      | [], [] -> true
      | o :: l, o' :: l' ->
          leftDecompose (gq, Less (o, o') :: d, d', p)
          && ltLexL (gq, Eq (o, o') :: d, d', l, l', p)

    and eqsL (gq, d, d', a, b, p) = match a, b with
      | [], [] -> true
      | o :: l, o' :: l' ->
          leftDecompose (gq, Eq (o, o') :: d, d', p)
          && eqsL (gq, d, d', l, l', p)

    and ltSimulL (gq, d, d', a, b, p) = match a, b with
      | [], [] -> leftDecompose (gq, d, d', p)
      | o :: l, o' :: l' ->
          leSimulL (gq, Less (o, o') :: d, d', l, l', p)
          || ltSimulL (gq, Eq (o, o') :: d, d', l, l', p)

    and leSimulL (gq, d, d', a, b, p) = match a, b with
      | [], [] -> leftDecompose (gq, d, d', p)
      | o :: l, o' :: l' ->
          leSimulL (gq, Leq (o, o') :: d, d', l, l', p)

    and ltAtomicL (gq, d, d', usVs, usVs', p) =
      ltAtomicLW (gq, d, d', usVs, (let a__, b__ = usVs' in Whnf.whnfEta a__ b__), p)

    and ltAtomicLW (a, d, d', b, c, p) = match a, b, c with
      | ((g, q) as gq), usVs, (us', ((I.Root _, s') as vs')) ->
          ltL (gq, d, d', usVs, (us', vs'), p)
      | ((g, q) as gq), ((u, s1), (v, s2)), ((I.Lam (_, u'), s1'), (I.Pi ((dec', _), v'), s2')) ->
          let d1 = shiftRCtx d (function s -> I.comp s I.shift) in
          let d1' = shiftACtx d' (function s -> I.comp s I.shift) in
          let usVs = ((u, I.comp s1 I.shift), (v, I.comp s2 I.shift)) in
          let usVs' = ((u', I.dot1 s1'), (v', I.dot1 s2')) in
          let p' = shiftP p (function s -> I.comp s I.shift) in
          ltAtomicL
            ( ( I.Decl (g, N.decLUName g (I.decSub dec' s2')),
                I.Decl (q, All) ),
              d1,
              d1',
              usVs,
              usVs',
              p' )

    and leAtomicL (gq, d, d', usVs, usVs', p) =
      leAtomicLW (gq, d, d', usVs, (let a__, b__ = usVs' in Whnf.whnfEta a__ b__), p)

    and leAtomicLW (a, d, d', b, c, p) = match a, b, c with
      | gq, usVs, (us', ((I.Root (h, s), s') as vs')) ->
          leL (gq, d, d', usVs, (us', vs'), p)
      | ((g, q) as gq), ((u, s1), (v, s2)), ((I.Lam (_, u'), s1'), (I.Pi ((dec', _), v'), s2')) ->
          let d1 = shiftRCtx d (function s -> I.comp s I.shift) in
          let d1' = shiftACtx d' (function s -> I.comp s I.shift) in
          let usVs = ((u, I.comp s1 I.shift), (v, I.comp s2 I.shift)) in
          let usVs' = ((u', I.dot1 s1'), (v', I.dot1 s2')) in
          let p' = shiftP p (function s -> I.comp s I.shift) in
          leAtomicL
            ( ( I.Decl (g, N.decLUName g (I.decSub dec' s2')),
                I.Decl (q, All) ),
              d1,
              d1',
              usVs,
              usVs',
              p' )

    and eqAtomicL (gq, d, d', usVs, usVs', p) =
      eqAtomicLW (gq, d, d', (let a__, b__ = usVs in Whnf.whnfEta a__ b__), (let a__, b__ = usVs' in Whnf.whnfEta a__ b__), p)

    and eqAtomicLW (gq, d, d', a, b, p) = match a, b with
      | (us, ((I.Root _, s) as vs)), (us', ((I.Root _, s') as vs')) ->
          eqL (gq, d, d', (us, vs), (us', vs'), p)
      | (us, ((I.Root _, s) as vs)), (us', ((I.Pi _, s') as vs')) ->
          true
      | (us, ((I.Pi _, s) as vs)), (us', ((I.Root _, s') as vs')) ->
          true
      | (us, ((I.Pi _, s) as vs)), (us', ((I.Pi _, s') as vs')) ->
          leftDecompose (gq, d, Eq ((us, vs), (us', vs')) :: d', p)

    and leL (gq, d, d', usVs, usVs', p) =
      ltAtomicL (gq, d, d', usVs, usVs', p)
      && eqAtomicL (gq, d, d', usVs, usVs', p)

    and ltL (gq, d, d', usVs, (us', vs'), p) =
      ltLW (gq, d, d', usVs, (Whnf.whnf us', vs'), p)

    and ltLW (a, d, d', usVs, b, p) = match a, b with
      | ((g, q) as gq), (((I.Root (I.BVar n, s'_), s') as us'), vs') ->
          begin if isAtomic (gq, us') then
            leftDecompose (gq, d, Less (usVs, (us', vs')) :: d', p)
          else
            let (I.Dec (_, v')) = I.ctxDec g n in
            ltSpineL (gq, d, d', usVs, ((s'_, s'), (v', I.id)), p)
          end
      | gq, ((I.Root (I.Const c, s'_), s'), vs') ->
          ltSpineL (gq, d, d', usVs, ((s'_, s'), (I.constType c, I.id)), p)
      | gq, ((I.Root (I.Def c, s'_), s'), vs') ->
          ltSpineL (gq, d, d', usVs, ((s'_, s'), (I.constType c, I.id)), p)

    and ltSpineL (gq, d, d', usVs, (ss', vs'), p) =
      ltSpineLW (gq, d, d', usVs, (ss', Whnf.whnf vs'), p)

    and ltSpineLW (gq, d, d', usVs, a, p) = match a with
      | ((I.Nil, _), _) -> true
      | ((I.SClo (s, s'), s''), vs') ->
          ltSpineL (gq, d, d', usVs, ((s, I.comp s' s''), vs'), p)
      | ((I.App (u', s'), s1'), (I.Pi ((I.Dec (_, v1'), _), v2'), s2')) ->
          leAtomicL (gq, d, d', usVs, ((u', s1'), (v1', s2')), p)
          && ltSpineL
               ( gq,
                 d,
                 d',
                 usVs,
                 ((s', s1'), (v2', I.Dot (I.Exp (I.EClo (u', s1')), s2'))),
                 p )

    and eqL (gq, d, d', usVs, usVs', p) =
      eqLW (gq, d, d', (let a__, b__ = usVs in Whnf.whnfEta a__ b__), (let a__, b__ = usVs' in Whnf.whnfEta a__ b__), p)

    and eqLW (a, d_, d', b, d, p) = match a, b, d with
      | gq, (us, ((I.Pi ((I.Dec (_, v2'), _), v'), s2') as vs)), (us', ((I.Pi ((I.Dec (_, v2''), _), v''), s2'') as vs')) ->
          leftDecompose (gq, d_, Eq ((us, vs), (us', vs')) :: d', p)
      | gq, (us, ((I.Pi ((I.Dec (_, v2'), _), v'), s2') as vs)), (us', ((I.Root _, s2'') as vs')) ->
          true
      | gq, (us, ((I.Root _, s2') as vs)), (us', ((I.Pi ((I.Dec (_, v2''), _), v''), s2'') as vs')) ->
          true
      | gq, (((I.Root (I.Const c, s_), s), vs) as usVs), (((I.Root (I.Const c', s'_), s'), vs') as usVs') ->
          begin if eqCid (c, c') then
            eqSpineL
              ( gq,
                d_,
                d',
                ((s_, s), (I.constType c, I.id)),
                ((s'_, s'), (I.constType c', I.id)),
                p )
          else true
          end
      | gq, (((I.Root (I.Const c, s_), s) as us), vs), (((I.Root (I.BVar n, s'_), s') as us'), vs') ->
          begin if isAtomic (gq, us') then
            leftDecompose (gq, d_, Eq ((us', vs'), (us, vs)) :: d', p)
          else true
          end
      | gq, (((I.Root (I.BVar n, s_), s) as us), vs), (((I.Root (I.Const c, s'_), s') as us'), vs') ->
          begin if isAtomic (gq, us) then
            leftDecompose (gq, d_, Eq ((us, vs), (us', vs')) :: d', p)
          else true
          end
      | gq, (((I.Root (I.Def c, s_), s), vs) as usVs), (((I.Root (I.Def c', s'_), s'), vs') as usVs') ->
          begin if eqCid (c, c') then
            eqSpineL
              ( gq,
                d_,
                d',
                ((s_, s), (I.constType c, I.id)),
                ((s'_, s'), (I.constType c', I.id)),
                p )
          else true
          end
      | gq, (((I.Root (I.Def c, s_), s) as us), vs), (((I.Root (I.BVar n, s'_), s') as us'), vs') ->
          begin if isAtomic (gq, us') then
            leftDecompose (gq, d_, Eq ((us', vs'), (us, vs)) :: d', p)
          else true
          end
      | gq, (((I.Root (I.BVar n, s_), s) as us), vs), (((I.Root (I.Def c, s'_), s') as us'), vs') ->
          begin if isAtomic (gq, us) then
            leftDecompose (gq, d_, Eq ((us, vs), (us', vs')) :: d', p)
          else true
          end
      | ((g, q) as gq), (((I.Root (I.BVar n, s_), s) as us), vs), (((I.Root (I.BVar n', s'_), s') as us'), vs') ->
          begin if n = n' then
            let (I.Dec (_, v')) = I.ctxDec g n in
            eqSpineL
              (gq, d_, d', ((s_, s), (v', I.id)), ((s'_, s'), (v', I.id)), p)
          else leftDecompose (gq, d_, Eq ((us, vs), (us', vs')) :: d', p)
          end
      | gq, usVs, usVs' ->
          leftDecompose (gq, d_, Eq (usVs, usVs') :: d', p)

    and eqSpineL (gq, d, d', (ss, vs), (ss', vs'), p) =
      eqSpineLW (gq, d, d', (ss, Whnf.whnf vs), (ss', Whnf.whnf vs'), p)

    and eqSpineLW (gq, d, d', ssVs, ssVs', p) = match ssVs, ssVs' with
      | ((Nil, s), vs), ((Nil, s'), vs') ->
          leftDecompose (gq, d, d', p)
      | ((I.SClo (s, s'), s''), vs), ssVs' ->
          eqSpineL (gq, d, d', ((s, I.comp s' s''), vs), ssVs', p)
      | ssVs, ((I.SClo (s'_, s'), s''), vs') ->
          eqSpineL (gq, d, d', ssVs, ((s'_, I.comp s' s''), vs'), p)
      | ((I.App (u, s), s1), (I.Pi ((I.Dec (_, v1), _), v2), s2)), ((I.App (u', s'), s1'), (I.Pi ((I.Dec (_, v1'), _), v2'), s2')) ->
          let d1 =
            Eq (R.Arg ((u, s1), (v1, s2)), R.Arg ((u', s1'), (v1', s2')))
            :: d
          in
          eqSpineL
            ( gq,
              d1,
              d',
              ((s, s1), (v2, I.Dot (I.Exp (I.EClo (u, s1)), s2))),
              ((s', s1'), (v2', I.Dot (I.Exp (I.EClo (u', s1')), s2'))),
              p )

    let deduce (g, q, d, p) = leftDecompose ((g, q), d, [], p)
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
