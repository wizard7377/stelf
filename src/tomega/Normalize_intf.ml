(* # 1 "src/tomega/Normalize.sig.ml" *)
open! Basis

module type NORMALIZE = sig
  module IntSyn : INTSYN
  module Tomega : TOMEGA

  val normalizeFor : Tomega.for_ * Tomega.sub -> Tomega.for_
  val normalizePrg : Tomega.prg * Tomega.sub -> Tomega.prg
  val normalizeSpine : Tomega.spine * Tomega.sub -> Tomega.spine
  val normalizeSub : Tomega.sub -> Tomega.sub
end
