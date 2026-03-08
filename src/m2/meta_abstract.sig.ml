open! Basis

(* Meta Abstraction *)
(* Author: Carsten Schuermann *)
module type METAABSTRACT = sig
  module MetaSyn : METASYN

  exception Error of string

  val abstract : MetaSyn.state_ -> MetaSyn.state_
end
(* signature METAABSTRACT *)
