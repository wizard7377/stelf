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

(* # 1 "src/tomega/Opsem.sig.ml" *)
open! Basis

module type OPSEM = sig
  (*! structure IntSyn : INTSYN !*)
  (*! structure Tomega : TOMEGA !*)
  exception NoMatch

  val evalPrg : Tomega.prg -> Tomega.prg
  val topLevel : Tomega.prg -> unit
  val createVarSub : Tomega.dec IntSyn.ctx -> Tomega.dec IntSyn.ctx -> Tomega.sub
  val matchSub : Tomega.dec IntSyn.ctx -> Tomega.sub -> Tomega.sub -> unit
end
