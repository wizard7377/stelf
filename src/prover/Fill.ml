(* # 1 "src/prover/Fill.sig.ml" *)
open! Basis

(* Filling: Version 1.4 *)
(* Author: Carsten Schuermann *)
include Fill_intf
(* signature FILL *)

(* # 1 "src/prover/Fill.fun.ml" *)
open! Basis

(* Filling *)
(* Author: Carsten Schuermann *)
(* Date: Thu Mar 16 13:08:33 2006 *)
module Fill (Fill__0 : sig
  module Data : Data.DATA

  (*! structure IntSyn' : INTSYN !*)
  (*! structure Tomega' : TOMEGA !*)
  (*! sharing Tomega'.IntSyn = IntSyn' !*)
  module State' : State.STATE

  (*! sharing State'.IntSyn = IntSyn' !*)
  (*! sharing State'.Tomega = Tomega' !*)
  module Abstract : ABSTRACT

  (*! sharing Abstract.IntSyn = IntSyn' !*)
  (*! sharing Abstract.Tomega = Tomega' !*)
  module TypeCheck : TYPECHECK

  (*! sharing TypeCheck.IntSyn = IntSyn' !*)
  module Search : Psearch.SEARCH

  (*! sharing Search.IntSyn = IntSyn' !*)
  (*! sharing Search.Tomega = Tomega' !*)
  module Whnf : WHNF

  (*! sharing Whnf.IntSyn = IntSyn' !*)
  module Unify : UNIFY
end) : FILL with module State = Fill__0.State' = struct
  (*! structure IntSyn = IntSyn' !*)
  (*! structure Tomega = Tomega' !*)
  module State = Fill__0.State'

  exception Error of string

  type operator_ =
    | FillWithConst of IntSyn.exp * IntSyn.cid
    | FillWithBVar of IntSyn.exp * int

  (* Representation Invariant:  FillWithConst (X, c) :
           X is an evar GX |- X : VX
           Sigma |- c : W
           and VX and W are unifiable
       *)
  module Unify = Fill__0.Unify

  (* Representation Invariant:  FillWithBVar (X, n) :
           X is an evar GX |- X : VX
           GX |- n : W
           and VX and W are unifiable
       *)
  type nonrec operator = operator_

  open! struct
    module S = State
    module T = Tomega
    module I = IntSyn

    exception Success of int

    let rec expand (S.FocusLF (I.EVar (r, g_, v_, _) as y_)) =
      let rec try_ = function
        | ((I.Root _, _) as vs_), fs_, o_ -> (
            try
              CsManager.trail (function () ->
                  begin
                    Unify.unify (g_, vs_, (v_, I.id));
                    o_ :: fs_
                  end)
            with Unify.Unify _ -> fs_)
        | (I.Pi ((I.Dec (_, v1_), _), v2_), s), fs_, o_ ->
            let x_ = I.newEVar (g_, I.EClo (v1_, s)) in
            try_ ((v2_, I.Dot (I.Exp x_, s)), fs_, o_)
        | (I.EClo (v_, s'), s), fs_, o_ -> try_ ((v_, I.comp (s', s)), fs_, o_)
      in
      let rec matchCtx = function
        | I.Null, _, fs_ -> fs_
        | I.Decl (g_, I.Dec (x, v_)), n, fs_ ->
            matchCtx
              ( g_,
                n + 1,
                try_ ((v_, I.Shift (n + 1)), fs_, FillWithBVar (y_, n + 1)) )
        | I.Decl (g_, I.NDec _), n, fs_ -> matchCtx (g_, n + 1, fs_)
      in
      let rec matchSig = function
        | [], fs_ -> fs_
        | I.Const c :: l_, fs_ ->
            matchSig
              (l_, try_ ((I.constType c, I.id), fs_, FillWithConst (y_, c)))
        | I.Def c :: l_, fs_ ->
            matchSig
              (l_, try_ ((I.constType c, I.id), fs_, FillWithConst (y_, c)))
        | _ :: l_, fs_ -> matchSig (l_, fs_)
      in
      matchCtx (g_, 0, matchSig (Index.lookup (I.targetFam v_), []))

    let rec apply = function
      | FillWithBVar ((I.EVar (r, g_, v_, _) as y_), n) ->
          let rec doit = function
            | ((I.Root _, _) as vs_), k -> begin
                Unify.unify (g_, vs_, (v_, I.id));
                k I.Nil
              end
            | (I.Pi ((I.Dec (_, v1_), _), v2_), s), k ->
                let x_ = I.newEVar (g_, I.EClo (v1_, s)) in
                doit
                  ( (v2_, I.Dot (I.Exp x_, s)),
                    function s_ -> k (I.App (x_, s_)) )
            | (I.EClo (v_, t), s), k -> doit ((v_, I.comp (t, s)), k)
          in
          let (I.Dec (_, w_)) = I.ctxDec (g_, n) in
          doit
            ( (w_, I.id),
              function
              | s_ -> Unify.unify (g_, (y_, I.id), (I.Root (I.BVar n, s_), I.id))
            )
      | FillWithConst ((I.EVar (r, g0_, v_, _) as y_), c) ->
          let rec doit = function
            | ((I.Root _, _) as vs_), k -> begin
                Unify.unify (g0_, vs_, (v_, I.id));
                k I.Nil
              end
            | (I.Pi ((I.Dec (_, v1_), _), v2_), s), k ->
                let x_ = I.newEVar (g0_, I.EClo (v1_, s)) in
                doit
                  ( (v2_, I.Dot (I.Exp x_, s)),
                    function s_ -> k (I.App (x_, s_)) )
          in
          let w_ = I.constType c in
          doit
            ( (w_, I.id),
              function
              | s_ ->
                  Unify.unify (g0_, (y_, I.id), (I.Root (I.Const c, s_), I.id))
            )

    let rec menu = function
      | FillWithBVar ((I.EVar (_, g_, _, _) as x_), n) -> begin
          match I.ctxLookup (Names.ctxName g_, n) with
          | I.Dec (Some x, _) ->
              (("Fill " ^ Names.evarName (g_, x_)) ^ " with variable ") ^ x
        end
      | FillWithConst ((I.EVar (_, g_, _, _) as x_), c) ->
          (("Fill " ^ Names.evarName (g_, x_)) ^ " with constant ")
          ^ IntSyn.conDecName (IntSyn.sgnLookup c)
  end

  (* expand' S = op'

       Invariant:
       If   |- S state
       then op' satifies representation invariant.
    *)
  (* Y is lowered *)
  (* matchCtx (G, n, Fs) = Fs'

           Invariant:
           If G0 = G, G' and |G'| = n and Fs a list of filling operators that
           satisfy the representation invariant, then Fs' is a list of filling operators
           that satisfy the representation invariant.
        *)
  (* apply op = ()

       Invariant:
       If op is a filling operator that satisfies the representation invariant.
       The apply operation is guaranteed to always succeed.
    *)
  (* Y is lowered *)
  (* Invariant : G |- s : G'   G' |- V : type *)
  (* Unify must succeed *)
  (* Unify must succeed *)
  (* menu op = s'

       Invariant:
       If op is a filling operator
       then s' is a string describing the operation in plain text
    *)
  (* Invariant: Context is named  --cs Fri Mar  3 14:31:08 2006 *)
  let expand = expand
  let apply = apply
  let menu = menu
end
(*! sharing Unify.IntSyn = IntSyn' !*)
(* local *)
(* functor Filling *)

(* # 1 "src/prover/Fill.sml.ml" *)
