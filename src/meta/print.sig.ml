open! Basis

(* Meta Printer Version 1.3 *)
(* Author: Carsten Schuermann *)
module type MTPRINT = sig
  module Formatter : FORMATTER
  module StateSyn : STATESYN

  exception Error of string

  val nameState : StateSyn.state_ -> StateSyn.state_
  val formatState : StateSyn.state_ -> Formatter.format
  val stateToString : StateSyn.state_ -> string
end
(* signature MTPRINT *)
