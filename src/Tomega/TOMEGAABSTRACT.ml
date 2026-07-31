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

(* # 1 "src/tomega/TomegaAbstract.sig.ml" *)
open! Basis

module type TOMEGAABSTRACT = sig
  exception Error of string

  val raiseFor :
    IntSyn.dec IntSyn.ctx * (Tomega.for_ * IntSyn.sub) -> Tomega.for_

  val raisePrg : IntSyn.dec IntSyn.ctx * Tomega.prg * Tomega.for_ -> Tomega.prg
  val raiseP : IntSyn.dec IntSyn.ctx * Tomega.prg * Tomega.for_ -> Tomega.prg
  val raiseF : IntSyn.dec IntSyn.ctx * (Tomega.for_ * IntSyn.sub) -> Tomega.for_
end
