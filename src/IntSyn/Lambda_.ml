open! Basis
open! Global
open! Global.Global_
open! Trail
open! Trail.Trail_
open! Table
open! Table.Table_

(* # 1 "src/lambda/Lambda_.sig.ml" *)

(** Top-level wiring for the core lambda subsystem Modules. *)

(* # 1 "src/lambda/Lambda_.fun.ml" *)

(* # 1 "src/lambda/Lambda_.sml.ml" *)
open! Basis
include Fgnopn
include Fgnopntable
include Order
include Intsyn_

(* Re-export module types before name shadowing *)
module type WHNF = Whnf.WHNF
module type CONV = Conv.CONV
module type CONSTRAINTS = Constraints.CONSTRAINTS
module type UNIFY = Unify.UNIFY
module type MATCH = Match.MATCH
module type ABSTRACT = Abstract.ABSTRACT
module type APPROX = Approx.APPROX

include Tomega

(* Instantiate core normalization/conversion modules explicitly; Tomega's
   private helper names are not exported through its .mli. *)
module Whnf_ = Whnf
module Conv_ = Conv
module Whnf = Whnf_.Whnf ()

module Conv = Conv_.Conv (struct
  module Whnf = Whnf
end)

type nonrec spine = IntSyn.spine

module Constraints = Constraints.MakeConstraints (Conv)
module UnifyNoTrail = Unify.MakeUnify (Whnf) (Notrail.NoTrail)
module UnifyTrail = Unify.MakeUnify (Whnf) (Trail)
module Match = Match.MakeMatch (Whnf) (UnifyTrail) (Trail)
module Abstract = Abstract.MakeAbstract (Whnf) (UnifyNoTrail) (Constraints)
module Approx = Approx.MakeApprox (Whnf)
