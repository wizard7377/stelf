(* # 1 "src/meta/Init.sig.ml" *)
open! Basis
open Funsyn
open Statesyn
open MtpGlobal
open MtpData
open Funprint

(* Initialization *)
(* Author: Carsten Schuermann *)

module type MTPINIT = sig
  (*! structure FunSyn : FUNSYN !*)
  module StateSyn : STATESYN

  exception Error of string

  (* Current restriction to non-mutual inductive theorems ! *)
  val init : FunSyn.for_ * StateSyn.order -> StateSyn.state list
end
