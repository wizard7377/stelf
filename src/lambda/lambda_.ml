(* # 1 "src/lambda/lambda_.sig.ml" *)

(* # 1 "src/lambda/lambda_.fun.ml" *)

(* # 1 "src/lambda/lambda_.sml.ml" *)
open! Basis
include Fgnopn
include Fgnopntable
include Order
include Intsyn

(* Re-export module types before name shadowing *)
module type WHNF = Whnf.WHNF
module type CONV = Conv.CONV
module type CONSTRAINTS = Constraints.CONSTRAINTS
module type UNIFY = Unify.UNIFY
module type MATCH = Match.MATCH
module type ABSTRACT = Abstract.ABSTRACT
module type APPROX = Approx.APPROX

include Tomega

(* Re-export Whnf and Conv under standard names *)
module Whnf = Whnf__
module Conv = Conv__

type nonrec spine = IntSyn.spine

(* Now in intsyn.fun *)
(*
structure IntSyn =
  IntSyn (structure Global = Global);
*)
(* Now in tomega.sml *)
(*
structure Whnf =
  Whnf (! structure IntSyn' = IntSyn !);

structure Conv =
  Conv (! structure IntSyn' = IntSyn !
	structure Whnf = Whnf);

structure Tomega : TOMEGA =
   Tomega (structure IntSyn' = IntSyn
	   structure Whnf = Whnf
	   structure Conv = Conv)
*)
module Constraints = Constraints.MakeConstraints (struct
  (*! structure IntSyn' = IntSyn !*) module Conv = Conv__
end)

module UnifyNoTrail = Unify.MakeUnify (struct
  (*! structure IntSyn' = IntSyn !*)
  module Whnf = Whnf__
  module Trail = Notrail.NoTrail
end)

module UnifyTrail = Unify.MakeUnify (struct
  (*! structure IntSyn' = IntSyn !*)
  module Whnf = Whnf__
  module Trail = Trail
end)

(* structure Normalize : NORMALIZE =  
  Normalize (! structure IntSyn' = IntSyn !
             ! structure Tomega' = Tomega !
             structure Whnf = Whnf)
 *)
module Match = Match.MakeMatch (struct
  module Whnf = Whnf__
  module Unify = UnifyTrail
  module Trail = Trail
end)

module Abstract = Abstract.MakeAbstract (struct
  module Whnf = Whnf__
  module Constraints = Constraints
  module Unify = UnifyNoTrail
end)

module Approx = Approx.MakeApprox (struct
  (*! structure IntSyn' = IntSyn !*) module Whnf = Whnf__
end)
