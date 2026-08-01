open! Basis
open! Global
open! Global.Global_
open! Trail
open! Trail.Trail_
open! Table
open! Table.Table_
open! Intsyn
open! Intsyn.Lambda_
open! Names
open! Names.Names_
open! Formatter
open! Formatter__Formatter_
open! Print
open! Print.Print_
open! Subordinate
open! Subordinate
open! Modes
open! Modes.Modes_
open! Typecheck
open! Typecheck.Typecheck_
open! Index
open! Index.Index_
open! Opsem
open! Opsem.Opsem_
open! Compile
open! Compile.Compile_
open! Heuristic
open! Heuristic.Heuristic_
open! Timing
open! Timing.Timing_
open! Solvers
open! Solvers.Solvers_
open! M2
open! M2.M2_

(* # 1 "src/meta/Weaken.sig.ml" *)
open! Basis

(* Weakening substitutions *)
(* Author: Carsten Schuermann *)
include WEAKEN
(* signature PRUNE *)

(* # 1 "src/meta/Weaken.fun.ml" *)
open! Basis

(* Weakening substitutions *)
(* Author: Carsten Schuermann *)
module Make_Weaken (Whnf : WHNF) : WEAKEN.WEAKEN = struct
  (*! structure IntSyn = IntSyn' !*)
  open! struct
    module I = IntSyn

    let strengthenExp u_ s = Whnf.normalize (Whnf.cloInv u_ s, I.id)
    let strengthenDec (I.Dec (name, v_)) s = I.Dec (name, strengthenExp v_ s)

    let rec strengthenCtx a b = match a, b with
      | I.Null, s -> (I.Null, s)
      | I.Decl (g_, d_), s ->
          let g'_, s' = strengthenCtx g_ s in
          (I.Decl (g'_, strengthenDec d_ s'), I.dot1 s')

    let strengthenSub s t = Whnf.compInv s t

    let rec strengthenSpine a b = match a, b with
      | I.Nil, t -> I.Nil
      | I.App (u_, s_), t ->
          I.App (strengthenExp u_ t, strengthenSpine s_ t)
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
module Weaken = Make_Weaken (Whnf)

(* # 1 "src/meta/Weaken.sml.ml" *)
