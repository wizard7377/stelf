(* # 1 "src/prover/Introduce.sig.ml" *)
open! Basis

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
      | T.UDec d_ -> T.UDec d_
      | T.PDec (name, f_, tc1, tc2) -> T.PDec (name, f_, tc1, stripTCOpt tc2)

    let rec strip = function
      | I.Null -> I.Null
      | I.Decl (psi, d_) -> I.Decl (strip psi, stripDec d_)

    let rec expand = function
      | S.Focus ((T.EVar (psi, r, T.All ((d_, _), f_), None, None, _) as r_), w_)
        ->
          let d'_ = TomegaNames.decName (psi, d_) in
          Some (r_, T.Lam (d'_, T.newEVar (I.Decl (strip psi, d'_), f_)))
      | S.Focus
          ( (T.EVar
               (psi, r, T.Ex (((I.Dec (_, v_) as d_), _), f_), None, None, _) as
             r_),
            w_ ) ->
          let x_ = I.newEVar (T.coerceCtx psi, v_) in
          let y_ = T.newEVar (psi, T.forSub (f_, T.Dot (T.Exp x_, T.id))) in
          Some (r_, T.PairExp (x_, y_))
      | S.Focus ((T.EVar (psi, r, True, None, None, _) as r_), w_) ->
          Some (r_, T.Unit)
      | S.Focus (T.EVar (psi, r, T.FClo (f_, s), tc1, tc2, x_), w_) ->
          expand (S.Focus (T.EVar (psi, r, T.forSub (f_, s), tc1, tc2, x_), w_))
      | S.Focus (T.EVar (psi, r, _, _, _, _), w_) -> None

    let apply (T.EVar (_, r, _, _, _, _), p_) = r := Some p_
    let menu (r, p_) = "Intro " ^ TomegaPrint.nameEVar r
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
