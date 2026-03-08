open! Basis

(* Normalizer for Delphin meta level *)
(* Author: Carsten Schuermann *)
module type NORMALIZE = sig
  module IntSyn : INTSYN
  module Tomega : TOMEGA

  val normalizeFor : Tomega.for_ * Tomega.sub_ -> Tomega.for_
  val normalizePrg : Tomega.prg_ * Tomega.sub_ -> Tomega.prg_
  val normalizeSpine : Tomega.spine_ * Tomega.sub_ -> Tomega.spine_
  val normalizeSub : Tomega.sub_ -> Tomega.sub_
end
