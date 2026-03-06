open! Basis;;
(* Qed *);;
(* Author: Carsten Schuermann *);;
module type QED = sig
                  module MetaSyn : METASYN
                  exception Error of string 
                  val subgoal : MetaSyn.state_ -> bool
                  end;;
(* signature QED *);;