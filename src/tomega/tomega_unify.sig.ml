open! Basis
module Tomega = Lambda_.Tomega

(* Unification on Formulas *)
(* Author: Carsten Schuermann *)
module type TOMEGAUNIFY = sig
  (*! structure IntSyn : INTSYN !*)
  (*! structure Tomega : TOMEGA !*)
  exception Unify of string

  val unifyFor : Tomega.dec_ IntSyn.ctx_ * Tomega.for_ * Tomega.for_ -> unit
end
(* Signature TOMEGATYPECHECK *)
