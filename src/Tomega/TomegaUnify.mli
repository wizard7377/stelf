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
include module type of TOMEGAUNIFY

module TomegaUnify (TomegaUnify__0 : sig
  (* Unification on Formulas *)
  (* Author: Carsten Schuermann *)
  (*! structure IntSyn' : INTSYN !*)
  (*! structure Tomega' : TOMEGA !*)
  (*! sharing Tomega'.IntSyn = IntSyn' !*)
  module Abstract : ABSTRACT

  (*! sharing Abstract.IntSyn = IntSyn' !*)
  module TypeCheck : TYPECHECK

  (*! sharing TypeCheck.IntSyn = IntSyn' !*)
  module Conv : CONV

  (*! sharing Conv.IntSyn = IntSyn' !*)
  module Normalize : Normalize.NORMALIZE

  (*! sharing Normalize.IntSyn = IntSyn' !*)
  (*! sharing Normalize.Tomega = Tomega' !*)
  module Whnf : WHNF

  (*! sharing Whnf.IntSyn = IntSyn' !*)
  module Print : PRINT

  (*! sharing Print.IntSyn = IntSyn' !*)
  module TomegaPrint : Tomegaprint.TOMEGAPRINT

  (*! sharing TomegaPrint.IntSyn = IntSyn' !*)
  (*! sharing TomegaPrint.Tomega = Tomega' !*)
  module Subordinate : Subordinate.Subordinate_.SUBORDINATE

  (*! sharing Subordinate.IntSyn = IntSyn' !*)
  module Weaken : WEAKEN.WEAKEN
end) : TOMEGAUNIFY
