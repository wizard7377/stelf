(* # 1 "src/meta/weaken.sig.ml" *)
open! Basis

(* Weakening substitutions *)
(* Author: Carsten Schuermann *)
include Weaken_intf
(* signature PRUNE *)

(* # 1 "src/meta/weaken.fun.ml" *)
open! Basis

(* Weakening substitutions *)
(* Author: Carsten Schuermann *)
module Make_Weaken (Weaken__0 : sig
  module Whnf : WHNF
end) : Weaken_intf.WEAKEN = struct
  (*! structure IntSyn = IntSyn' !*)
  open! struct
    module I = IntSyn

    let rec strengthenExp (u_, s) = Whnf.normalize (Whnf.cloInv (u_, s), I.id)

    let rec strengthenDec (I.Dec (name, v_), s) =
      I.Dec (name, strengthenExp (v_, s))

    let rec strengthenCtx = function
      | I.Null, s -> (I.Null, s)
      | I.Decl (g_, d_), s ->
          let g'_, s' = strengthenCtx (g_, s) in
          (I.Decl (g'_, strengthenDec (d_, s')), I.dot1 s')

    let rec strengthenSub (s, t) = Whnf.compInv (s, t)

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

module Weaken = Make_Weaken (struct
  module Whnf = Whnf
end)

(* # 1 "src/meta/weaken.sml.ml" *)
