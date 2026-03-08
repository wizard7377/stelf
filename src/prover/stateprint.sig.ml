open! Basis

(* Meta Printer Version 1.3 *)
(* Author: Carsten Schuermann *)
module type STATEPRINT = sig
  module Formatter : FORMATTER

  (*! structure IntSyn : INTSYN !*)
  (*! structure Tomega : TOMEGA !*)
  module State : STATE

  exception Error of string

  val nameState : State.state_ -> State.state_
  val formatState : State.state_ -> Formatter.format
  val stateToString : State.state_ -> string
end
(* signature STATEPRINT *)
