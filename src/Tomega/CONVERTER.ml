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

(* # 1 "src/tomega/Converter.sig.ml" *)
open! Basis

module type CONVERTER = sig
  (*! structure IntSyn : INTSYN !*)
  (*! structure Tomega : TOMEGA !*)
  exception Error of string
  exception Error' of Tomega.sub

  val convertFor : IntSyn.cid list -> Tomega.for_
  val convertPrg : IntSyn.cid list -> Tomega.prg

  val installPrg :
    IntSyn.cid list ->
    IntSyn.cid * Tomega.lemma list * Tomega.lemma list (* projections *)

  (* selections *)
  val convertGoal : Tomega.dec IntSyn.ctx -> IntSyn.exp -> Tomega.prg
end
