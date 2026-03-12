open! Basis

(* Fixed Point *)
(* Author: Carsten Schuermann *)
module FixedPoint (FixedPoint__0 : sig
  module State' : State.STATE
  end) : FIXEDPOINT with module State = FixedPoint__0.State' = struct
  (*! structure IntSyn = IntSyn' !*)
  (*! structure Tomega = Tomega' !*)
  module State = FixedPoint__0.State'

  open! struct
    module S = FixedPoint__0.State'
    module T = Tomega
    module I = IntSyn

    exception Error = S.Error

    type nonrec operator = T.prg_ option ref * T.prg_

    let rec expand (S.Focus (T.EVar (psi_, r, f_, _, tCs_, _), w_), o_) =
      let (I.NDec x) = Names.decName (T.coerceCtx psi_, I.NDec None) in
      let d_ = T.PDec (x, f_, None, None) in
      let x_ = T.newEVar (I.Decl (psi_, d_), T.forSub (f_, T.Shift 1)) in
      (r, T.Rec (d_, x_))

    let rec apply (r, p_) = r := Some p_
    let rec menu _ = "Recursion introduction"
  end

  (* expand S = S'

       Invariant:
       If   S = (Psi |>  F)
       and  F does not start with an all quantifier
       then S' = (Psi, xx :: F |> F)
    *)
  (*        val D = T.PDec (SOME ""IH"" , F, SOME O, SOME O) *)
  (* apply O = S

       Invariant:
       O = S
    *)
  (* should be trailed -cs Thu Apr 22 11:20:32 2004 *)
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
(*! structure IntSyn' : INTSYN !*)
(*! structure Tomega' : TOMEGA !*)
(*! sharing Tomega'.IntSyn = IntSyn' !*)
(*! sharing State'.IntSyn = IntSyn' !*)
(*! sharing State'.Tomega = Tomega' !*)
