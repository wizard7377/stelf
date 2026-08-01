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

(* # 1 "src/tomega/TomegaTypecheck.sig.ml" *)
open! Basis

module type TOMEGATYPECHECK = sig
  exception Error of string

  val checkCtx : Tomega.dec IntSyn.ctx -> unit
  val checkFor : Tomega.dec IntSyn.ctx -> Tomega.for_ -> unit
  val checkPrg : Tomega.dec IntSyn.ctx -> Tomega.prg * Tomega.for_ -> unit

  val checkSub :
    Tomega.dec IntSyn.ctx -> Tomega.sub -> Tomega.dec IntSyn.ctx -> unit
end
