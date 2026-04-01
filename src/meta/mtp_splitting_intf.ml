(* # 1 "src/meta/splitting.sig.ml" *)
open! Basis
open Funsyn
open Statesyn
open Mtp_global
open Mtp_abstract
open Mtp_print
open Funtypecheck

(* Splitting : Version 1.3 *)
(* Author: Carsten Schuermann *)

module type MTPSPLITTING = sig
  module StateSyn : STATESYN

  exception Error of string

  type operator

  val expand : StateSyn.state -> operator list
  val applicable : operator -> bool
  val apply : operator -> StateSyn.state list
  val menu : operator -> string
  val index : operator -> int
  val compare : operator * operator -> order
end
