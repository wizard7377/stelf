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

  type nonrec operator

  val expand : StateSyn.state_ -> operator
  val apply : operator -> StateSyn.state_
  val menu : operator -> string
end
(* signature MTPRECURSION *)
