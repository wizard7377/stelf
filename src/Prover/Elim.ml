open! Tomega_lib.Tomega_
open! Intsyn.Lambda_
open! Names.Names_
open! Typecheck.Typecheck_

(* # 1 "src/prover/Elim.sig.ml" *)

(* ELIM: Version 1.4 *)
(* Author: Carsten Schuermann *)
include ELIM
(* signature ELIM *)

(* # 1 "src/prover/Elim.fun.ml" *)
open! Basis

(* Elim *)
(* Author: Carsten Schuermann *)
(* Date: Thu Mar 16 13:39:26 2006 *)
exception Error of string

let () =
  Printexc.register_printer (function Error msg -> Some msg | _ -> None)

module Elim (Elim__0 : sig
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
  module Whnf : WHNF

  (*! sharing Whnf.IntSyn = IntSyn' !*)
  module Unify : UNIFY
end) : ELIM with module State = Elim__0.State' = struct
  (*! structure IntSyn = IntSyn' !*)
  (*! structure Tomega = Tomega' !*)
  module State = Elim__0.State'

  exception Error = Error

  type operator_ = Local of Tomega.prg * int
  type nonrec operator = operator_

  open! struct
    module S = State
    module T = Tomega
    module I = IntSyn

    exception Success of int

    let stripTC tc = tc
    let stripTCOpt = function None -> None | Some tc -> Some (stripTC tc)

    let stripDec = function
      | T.UDec d -> T.UDec d
      | T.PDec (name, f, tc1, tc2) -> T.PDec (name, f, tc1, stripTCOpt tc2)

    let rec strip = function
      | I.Null -> I.Null
      | I.Decl (psi, d) -> I.Decl (strip psi, stripDec d)

    let expand (S.Focus ((T.EVar (psi, r, g, v, _, _) as y), w)) =
      let rec matchCtx (a, n, fs) = match a with
        | I.Null -> fs
        | I.Decl (g, T.PDec (x, f, _, _)) ->
            matchCtx (g, n + 1, Local (y, n) :: fs)
        | I.Decl (g, T.UDec _) -> matchCtx (g, n + 1, fs)
      in
      matchCtx (psi, 1, [])

    let rec apply = function
      | Local ((T.EVar (psi, r, g, None, None, _) as r_), n) ->
          let (T.PDec (_, f0, _, _)) = T.ctxDec psi n in
          begin match f0 with
          | T.All ((T.UDec (I.Dec (_, v)), _), f) ->
              let x_ = I.newEVar (T.coerceCtx (strip psi)) v in
              let (I.NDec x) = Names.decName (T.coerceCtx psi) (I.NDec None) in
              let d =
                T.PDec (x, T.forSub f (T.Dot (T.Exp x_, T.id)), None, None)
              in
              let psi' = I.Decl (psi, d) in
              let y = T.newEVar (strip psi') (T.forSub g T.shift) in
              r :=
                Some (T.Let (d, T.Redex (T.Var n, T.AppExp (x_, T.Nil)), y))
          | T.Ex ((d1, _), f) ->
              let d1' = Names.decName (T.coerceCtx psi) d1 in
              let psi' = I.Decl (psi, T.UDec d1') in
              let (I.NDec x) = Names.decName (T.coerceCtx psi') (I.NDec None) in
              let d2 = T.PDec (x, f, None, None) in
              let psi'' = I.Decl (psi', d2) in
              let y = T.newEVar (strip psi'') (T.forSub g (T.Shift 2)) in
              r := Some (T.LetPairExp (d1', d2, T.Var n, y))
          | True ->
              let y = T.newEVar (strip psi) g in
              r := Some (T.LetUnit (T.Var n, y))
          end
      | Local (T.EVar (psi, r, T.FClo (f, s), tc1, tc2, x), n) ->
          apply (Local (T.EVar (psi, r, T.forSub f s, tc1, tc2, x), n))

    let menu (Local ((T.EVar (psi, _, _, _, _, _) as x_), n)) =
      begin match I.ctxLookup psi n with
      | T.PDec (Some x, _, _, _) ->
          (("Elim " ^ TomegaPrint.nameEVar x_) ^ " with variable ") ^ x
      end
  end

  (* These lines need to move *)
  (* fun stripTC (T.Abs (_, TC)) = TC *)
  (* expand' S = op'

       Invariant:
       If   |- S state
       then op' is an operator which performs the filling operation
    *)
  (* Y is lowered *)
  (* apply op = B'

       Invariant:
       If op is a filling operator
       then B' holds iff the filling operation was successful
    *)
  (* the NONE, NONE may breach an invariant *)
  (* revisit when we add subterm orderings *)
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
(* functor elim *)

(* # 1 "src/prover/Elim.sml.ml" *)
