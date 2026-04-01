(* # 1 "src/tomega/tomega_unify.sig.ml" *)
open! Basis

module type TOMEGAUNIFY = sig
  (*! structure IntSyn : INTSYN !*)
  (*! structure Tomega : TOMEGA !*)
  exception Unify of string

  val unifyFor : Tomega.dec IntSyn.ctx * Tomega.for_ * Tomega.for_ -> unit
end
