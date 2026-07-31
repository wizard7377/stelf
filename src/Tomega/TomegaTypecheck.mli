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
include module type of TOMEGATYPECHECK

module TomegaTypeCheck (TomegaTypeCheck__0 : sig
  (* Type checking for Tomega *)
  (* Author: Carsten Schuermann *)
  (* Modified: Yu Liao *)
  module Abstract : ABSTRACT
  module TypeCheck : TYPECHECK
  module Conv : CONV
  module Whnf : WHNF
  module Print : PRINT
  module TomegaPrint : Tomegaprint.TOMEGAPRINT
  module Subordinate : Subordinate.Subordinate_.SUBORDINATE
  module Weaken : WEAKEN.WEAKEN
  module TomegaAbstract : TOMEGAABSTRACT.TOMEGAABSTRACT
end) : TOMEGATYPECHECK
