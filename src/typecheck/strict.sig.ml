open! Basis

(* Checking Definitions for Strictness *)
(* Author: Carsten Schuermann *)
module type STRICT = sig
  (*! structure IntSyn : INTSYN !*)
  (*! structure Paths : PATHS !*)
  exception Error of string

  val check : (IntSyn.exp_ * IntSyn.exp_) * Paths.occConDec option -> unit
  val checkType : (int * IntSyn.exp_) * Paths.occConDec option -> unit
end
(* signature STRICT *)
