open! Basis
open Funsyn
open Statesyn
open Mtp_global
open Mtp_data
open Mtp_search

(* Filling: Version 1.3 *)
(* Author: Carsten Schuermann *)
module type MTPFILLING = sig
  (*! structure FunSyn : FUNSYN !*)
  module StateSyn : STATESYN

  exception Error of string
  exception TimeOut

  type nonrec operator

  val expand : StateSyn.state_ -> operator
  val apply : operator -> int * FunSyn.pro_
  val menu : operator -> string
end
(* signature MTPFILLING *)
