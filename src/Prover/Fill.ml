open! Intsyn.Lambda_
open! Names.Names_
open! Index.Index_
open! Typecheck.Typecheck_
open! Solvers.Solvers_

(* # 1 "src/prover/Fill.sig.ml" *)

(* Filling: Version 1.4 *)
(* Author: Carsten Schuermann *)
include FILL
(* signature FILL *)

(* # 1 "src/prover/Fill.fun.ml" *)
open! Basis

(* Filling *)
(* Author: Carsten Schuermann *)
(* Date: Thu Mar 16 13:08:33 2006 *)
exception Error of string

let () =
  Printexc.register_printer (function Error msg -> Some msg | _ -> None)

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

  exception Error = Error

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

    let expand (S.FocusLF (I.EVar (r, g, v, _) as y)) =
      let rec try_ (a, fs, o) = match a with
        | ((I.Root _, _) as vs) -> (
            try
              CsManager.trail (function () ->
                  begin
                    Unify.unify g vs (v, I.id);
                    o :: fs
                  end)
            with Unify.Unify _ -> fs)
        | (I.Pi ((I.Dec (_, v1), _), v2), s) ->
            let x = I.newEVar g (I.EClo (v1, s)) in
            try_ ((v2, I.Dot (I.Exp x, s)), fs, o)
        | (I.EClo (v, s'), s) -> try_ ((v, I.comp s' s), fs, o)
      in
      let rec matchCtx (a, n, fs) = match a with
        | I.Null -> fs
        | I.Decl (g, I.Dec (x, v)) ->
            matchCtx
              ( g,
                n + 1,
                try_ ((v, I.Shift (n + 1)), fs, FillWithBVar (y, n + 1)) )
        | I.Decl (g, I.NDec _) -> matchCtx (g, n + 1, fs)
      in
      let rec matchSig (a, fs) = match a with
        | [] -> fs
        | I.Const c :: l ->
            matchSig
              (l, try_ ((I.constType c, I.id), fs, FillWithConst (y, c)))
        | I.Def c :: l ->
            matchSig
              (l, try_ ((I.constType c, I.id), fs, FillWithConst (y, c)))
        | _ :: l -> matchSig (l, fs)
      in
      matchCtx (g, 0, matchSig (Index.lookup (I.targetFam v), []))

    let apply = function
      | FillWithBVar ((I.EVar (r, g, v, _) as y), n) ->
          let rec doit (a, k) = match a with
            | ((I.Root _, _) as vs) -> begin
                Unify.unify g vs (v, I.id);
                k I.Nil
              end
            | (I.Pi ((I.Dec (_, v1), _), v2), s) ->
                let x = I.newEVar g (I.EClo (v1, s)) in
                doit
                  ( (v2, I.Dot (I.Exp x, s)),
                    function s -> k (I.App (x, s)) )
            | (I.EClo (v, t), s) -> doit ((v, I.comp t s), k)
          in
          let (I.Dec (_, w)) = I.ctxDec g n in
          doit
            ( (w, I.id),
              function
              | s -> Unify.unify g (y, I.id) (I.Root (I.BVar n, s), I.id)
            )
      | FillWithConst ((I.EVar (r, g0, v, _) as y), c) ->
          let rec doit (a, k) = match a with
            | ((I.Root _, _) as vs) -> begin
                Unify.unify g0 vs (v, I.id);
                k I.Nil
              end
            | (I.Pi ((I.Dec (_, v1), _), v2), s) ->
                let x = I.newEVar g0 (I.EClo (v1, s)) in
                doit
                  ( (v2, I.Dot (I.Exp x, s)),
                    function s -> k (I.App (x, s)) )
          in
          let w = I.constType c in
          doit
            ( (w, I.id),
              function
              | s ->
                  Unify.unify g0 (y, I.id) (I.Root (I.Const c, s), I.id)
            )

    let menu = function
      | FillWithBVar ((I.EVar (_, g, _, _) as x_), n) ->
          begin match I.ctxLookup (Names.ctxName g) n with
          | I.Dec (Some x, _) ->
              (("Fill " ^ Names.evarName g x_) ^ " with variable ") ^ x
          end
      | FillWithConst ((I.EVar (_, g, _, _) as x), c) ->
          (("Fill " ^ Names.evarName g x) ^ " with constant ")
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
