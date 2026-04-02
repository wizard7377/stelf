(* # 1 "src/meta/Recursion.sig.ml" *)
open! Basis
open Funsyn
open Statesyn
open MtpGlobal
open MtpAbstract
open MtpPrint
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
