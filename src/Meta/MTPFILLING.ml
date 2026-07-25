(* # 1 "src/meta/Filling.sig.ml" *)
open! Basis
open Funsyn
open Statesyn
open MtpGlobal
open MtpData
open MtpSearch

(* Filling: Version 1.3 *)
(* Author: Carsten Schuermann *)

module type MTPFILLING = sig
  (*! structure FunSyn : FUNSYN !*)
  module StateSyn : STATESYN

  exception Error of string
  exception TimeOut

  type operator

  val expand : StateSyn.state -> operator
  val apply : operator -> int * FunSyn.pro
  val menu : operator -> string
end
