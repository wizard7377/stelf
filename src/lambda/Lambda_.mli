(* # 1 "src/lambda/Lambda_.sig.ml" *)

(** Top-level wiring for the core lambda subsystem Modules. *)

(* # 1 "src/lambda/Lambda_.fun.ml" *)

(* # 1 "src/lambda/Lambda_.sml.ml" *)
open! Basis
include module type of Fgnopn
include module type of Fgnopntable
include module type of Order
include module type of Intsyn
include module type of Tomega

(* Re-export module types before name shadowing *)
module type WHNF = Whnf.WHNF
module type CONV = Conv.CONV
module type CONSTRAINTS = Constraints.CONSTRAINTS
module type UNIFY = Unify.UNIFY
module type MATCH = Match.MATCH
module type ABSTRACT = Abstract.ABSTRACT
module type APPROX = Approx.APPROX

module Whnf : WHNF
module Conv : CONV
type spine = IntSyn.spine
module Constraints : CONSTRAINTS
module UnifyNoTrail : UNIFY
module UnifyTrail : UNIFY
module Match : MATCH
module Abstract : ABSTRACT
module Approx : APPROX
