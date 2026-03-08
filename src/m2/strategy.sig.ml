open! Basis

(* Strategy *)
(* Author: Carsten Schuermann *)
module type STRATEGY = sig
  module MetaSyn : METASYN

  val run : MetaSyn.state_ list -> MetaSyn.state_ list * MetaSyn.state_ list
end
(* open cases -> remaining cases * solved cases *)
(* signature STRATEGY *)
