open! Intsyn.Lambda_

(* # 1 "src/prover/Weaken.sig.ml" *)

(* Weakening substitutions *)
(* Author: Carsten Schuermann *)
include PWEAKEN
(* signature PRUNE *)

(* # 1 "src/prover/Weaken.fun.ml" *)

(* Weakening substitutions *)
(* Author: Carsten Schuermann *)
module Weaken (Weaken__0 : sig
  module Whnf : WHNF
end) : WEAKEN = struct
  (*! structure IntSyn = IntSyn' !*)
  open! struct
    module I = IntSyn

    let strengthenExp u s = Whnf.normalize (Whnf.cloInv u s, I.id)
    let strengthenDec (I.Dec (name, v)) s = I.Dec (name, strengthenExp v s)

    let rec strengthenCtx a b = match a, b with
      | I.Null, s -> (I.Null, s)
      | I.Decl (g, d), s ->
          let g', s' = strengthenCtx g s in
          (I.Decl (g', strengthenDec d s'), I.dot1 s')

    let strengthenSub s t = Whnf.compInv s t

    let rec strengthenSpine a b = match a, b with
      | I.Nil, t -> I.Nil
      | I.App (u, s), t ->
          I.App (strengthenExp u t, strengthenSpine s t)
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
