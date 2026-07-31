open! Basis
open! Global
open! Global.Global_
open! Intsyn
open! Intsyn.Lambda_
open! Worldcheck
open! Worldcheck.Worldcheck_
open! Cover
open! Cover.Cover_
open! Formatter
open! Formatter__Formatter_
open! Names
open! Names.Names_
open! Print
open! Print.Print_
open! Typecheck
open! Typecheck.Typecheck_
open! Subordinate
open! Subordinate
open! Meta
open! Meta.Meta_
open! Modes
open! Modes.Modes_
open! Trail
open! Trail.Trail_

(* # 1 "src/tomega/Normalize.sig.ml" *)
open! Basis

module type NORMALIZE = sig
  module IntSyn : INTSYN.INTSYN
  module Tomega : TOMEGA

  val normalizeFor : Tomega.for_ * Tomega.sub -> Tomega.for_
  val normalizePrg : Tomega.prg * Tomega.sub -> Tomega.prg
  val normalizeSpine : Tomega.spine * Tomega.sub -> Tomega.spine
  val normalizeSub : Tomega.sub -> Tomega.sub
end
