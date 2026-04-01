(* # 1 "src/meta/recursion.sig.ml" *)
open! Basis
open Funsyn
open Statesyn
open Mtp_global
open Mtp_abstract
open Mtp_print
open Funtypecheck
open Funprint

(* Recursion: Version 1.3 *)
(* Author: Carsten Schuermann *)

module type MTPRECURSION = sig
  module StateSyn : STATESYN

  exception Error of string

  type operator

  val expand : StateSyn.state -> operator
  val apply : operator -> StateSyn.state
  val menu : operator -> string
end
