(* # 1 "src/meta/print.sig.ml" *)
open! Basis
open Funsyn
open Statesyn
open Funprint

(* Meta Printer Version 1.3 *)
(* Author: Carsten Schuermann *)

module type MTPRINT = sig
  module Formatter : FORMATTER
  module StateSyn : STATESYN

  exception Error of string

  val nameState : StateSyn.state -> StateSyn.state
  val formatState : StateSyn.state -> Formatter.format
  val stateToString : StateSyn.state -> string
end
