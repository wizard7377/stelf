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

(* # 1 "src/prover/Weaken.sig.ml" *)
open! Basis

(* Weakening substitutions *)
(* Author: Carsten Schuermann *)
include PWEAKEN
(* signature PRUNE *)

(* # 1 "src/prover/Weaken.fun.ml" *)
open! Basis

(* Weakening substitutions *)
(* Author: Carsten Schuermann *)
module Weaken (Weaken__0 : sig
  module Whnf : WHNF
end) : WEAKEN = struct
  (*! structure IntSyn = IntSyn' !*)
  open! struct
    module I = IntSyn

    let strengthenExp (u_, s) = Whnf.normalize (Whnf.cloInv (u_, s), I.id)
    let strengthenDec (I.Dec (name, v_), s) = I.Dec (name, strengthenExp (v_, s))

    let rec strengthenCtx = function
      | I.Null, s -> (I.Null, s)
      | I.Decl (g_, d_), s ->
          let g'_, s' = strengthenCtx (g_, s) in
          (I.Decl (g'_, strengthenDec (d_, s')), I.dot1 s')

    let strengthenSub (s, t) = Whnf.compInv (s, t)

    let rec strengthenSpine = function
      | I.Nil, t -> I.Nil
      | I.App (u_, s_), t ->
          I.App (strengthenExp (u_, t), strengthenSpine (s_, t))
  end

  (* strengthenExp (U, s) = U'

       Invariant:
       If   G |- s : G'
       and  G |- U : V
       then G' |- U' = U[s^-1] : V [s^-1]
    *)
  (* strengthenDec (x:V, s) = x:V'

       Invariant:
       If   G |- s : G'
       and  G |- V : L
       then G' |- V' = V[s^-1] : L
    *)
  (* strengthenCtx (G, s) = (G', s')

       If   G0 |- G ctx
       and  G0 |- s G1
       then G1 |- G' = G[s^-1] ctx
       and  G0 |- s' : G1, G'
    *)
  let strengthenExp = strengthenExp
  let strengthenSpine = strengthenSpine
  let strengthenDec = strengthenDec
  let strengthenCtx = strengthenCtx
  let strengthenSub = strengthenSub
end
(*! structure IntSyn' : INTSYN !*)
(*! sharing Whnf.IntSyn = IntSyn' !*)
(* functor Weaken *)

(* # 1 "src/prover/Weaken.sml.ml" *)
