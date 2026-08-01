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
include module type of TOMEGAABSTRACT

module TomegaAbstract (TomegaAbstract__0 : sig
  (* Converter from relational representation to a functional
   representation of proof terms *)
  (* Author: Carsten Schuermann *)
  module Global : GLOBAL

  val abstract_raiseType : IntSyn.dctx -> IntSyn.exp -> IntSyn.exp
  val abstract_raiseTerm : IntSyn.dctx -> IntSyn.exp -> IntSyn.exp

  module Whnf : WHNF
  module Subordinate : Subordinate.Subordinate_.SUBORDINATE
end) : TOMEGAABSTRACT
