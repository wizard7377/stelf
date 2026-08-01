open! Basis
open! Tomega_lib
open! Tomega_lib.Tomega_
open! Intsyn
open! Intsyn.Lambda_
open! Global
open! Global.Global_
open! Names
open! Names.Names_
open! Print
open! Print.Print_
open! Index
open! Index.Index_
open! Modes
open! Modes.Modes_
open! Typecheck
open! Typecheck.Typecheck_
open! Table
open! Table.Table_
open! Subordinate
open! Subordinate
open! Solvers
open! Solvers.Solvers_
open! Opsem
open! Trail
open! Trail.Trail_
open! Compile
open! Compile.Compile_
open! Worldcheck
open! Worldcheck.Worldcheck_
open! Formatter
open! Formatter__Formatter_
open! Timing
open! Timing.Timing_

(* # 1 "src/prover/Fixedpoint.sig.ml" *)
open! Basis

(* Splitting: Version 1.4 *)
(* Author: Carsten Schuermann *)
include FIXEDPOINT
(* signature Fixed Point *)

(* # 1 "src/prover/Fixedpoint.fun.ml" *)
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

    type nonrec operator = T.prg option ref * T.prg

    let expand (S.Focus (T.EVar (psi, r, f_, _, tCs, _), w_)) o_ =
      let (I.NDec x) = Names.decName (T.coerceCtx psi) (I.NDec None) in
      let d_ = T.PDec (x, f_, None, None) in
      let x_ = T.newEVar (I.Decl (psi, d_)) (T.forSub f_ (T.Shift 1)) in
      (r, T.Rec (d_, x_))

    let apply r p_ = r := Some p_
    let menu _ = "Recursion introduction"
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

(* # 1 "src/prover/Fixedpoint.sml.ml" *)
