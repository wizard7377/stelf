open! Tomega_lib
open! Tomega_lib.Tomega_
open! Intsyn.Lambda_

(* # 1 "src/prover/Introduce.sig.ml" *)

(* Introduce: Version 1.4 *)
(* Author: Carsten Schuermann *)
include INTRODUCE
(* signature INTRODUCE *)

(* # 1 "src/prover/Introduce.fun.ml" *)
open! Basis

module Introduce (Introduce__0 : sig
  (* Introduce *)
  (* Author: Carsten Schuermann *)
  (*! structure IntSyn' : INTSYN !*)
  (*! structure Tomega' : TOMEGA !*)
  (*! sharing Tomega'.IntSyn = IntSyn' !*)
  module State' : State.STATE
  module TomegaNames : Tomeganames.TOMEGANAMES
end) : INTRODUCE with module State = Introduce__0.State' = struct
  (*! structure IntSyn = IntSyn' !*)
  (*! structure Tomega = Tomega' !*)
  module State = Introduce__0.State'
  module TomegaNames = Introduce__0.TomegaNames

  open! struct
    module S = Introduce__0.State'
    module T = Tomega
    module I = IntSyn

    exception Error = S.Error

    type nonrec operator = T.prg * T.prg

    let stripTC tc = tc
    let stripTCOpt = function None -> None | Some tc -> Some (stripTC tc)

    let stripDec = function
      | T.UDec d -> T.UDec d
      | T.PDec (name, f, tc1, tc2) -> T.PDec (name, f, tc1, stripTCOpt tc2)

    let rec strip = function
      | I.Null -> I.Null
      | I.Decl (psi, d) -> I.Decl (strip psi, stripDec d)

    let rec expand = function
      | S.Focus ((T.EVar (psi, r, T.All ((d, _), f), None, None, _) as r_), w)
        ->
          let d' = TomegaNames.decName psi d in
          Some (r_, T.Lam (d', T.newEVar (I.Decl (strip psi, d')) f))
      | S.Focus
          ( (T.EVar
               (psi, r, T.Ex (((I.Dec (_, v) as d), _), f), None, None, _) as
             r_),
            w ) ->
          let x = I.newEVar (T.coerceCtx psi) v in
          let y = T.newEVar psi (T.forSub f (T.Dot (T.Exp x, T.id))) in
          Some (r_, T.PairExp (x, y))
      | S.Focus ((T.EVar (psi, r, True, None, None, _) as r_), w) ->
          Some (r_, T.Unit)
      | S.Focus (T.EVar (psi, r, T.FClo (f, s), tc1, tc2, x), w) ->
          expand (S.Focus (T.EVar (psi, r, T.forSub f s, tc1, tc2, x), w))
      | S.Focus (T.EVar (psi, r, _, _, _, _), w) -> None

    let apply (T.EVar (_, r, _, _, _, _), p) = r := Some p
    let menu (r, p) = "Intro " ^ TomegaPrint.nameEVar r
  end

  (*    fun stripTC (T.Abs (_, TC)) = TC *)
  (* expand S = S'

       Invariant:
       If   S = (Psi |> all x1:A1 .... xn: An. F)
       and  F does not start with an all quantifier
       then S' = (Psi, x1:A1, ... xn:An |> F)
    *)
  (* apply O = S

       Invariant:
       O = S
    *)
  (* need to trail for back *)
  (* menu O = s

       Invariant:
       s = ""Apply universal introduction rules""
    *)
  exception Error = Error

  type nonrec operator = operator

  let expand = expand
  let apply = apply
  let menu = menu
end
(*! sharing State'.IntSyn = IntSyn' !*)
(*! sharing State'.Tomega = Tomega' !*)

(* # 1 "src/prover/Introduce.sml.ml" *)
