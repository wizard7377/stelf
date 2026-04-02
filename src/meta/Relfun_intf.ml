open! Basis
open Modetable
open Funweaken
open Funnames
open Funsyn

(* Converter from relational representation to a functional
   representation of proof terms *)
(* Author: Carsten Schuermann *)
module type RELFUN = sig
  (*! structure FunSyn : FUNSYN !*)
  exception Error of string

  val convertFor : IntSyn.cid list -> FunSyn.for_
  val convertPro : IntSyn.cid list -> FunSyn.pro
end
