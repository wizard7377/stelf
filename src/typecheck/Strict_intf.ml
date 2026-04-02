(* # 1 "src/typecheck/Strict.sig.ml" *)
open! Basis

(* Checking Definitions for Strictness *)
(* Author: Carsten Schuermann *)

module type STRICT = sig
  (*! structure IntSyn : INTSYN !*)
  (*! structure Paths : PATHS !*)
  exception Error of string

  val check : (IntSyn.exp * IntSyn.exp) * Paths.occConDec option -> unit
  val checkType : (int * IntSyn.exp) * Paths.occConDec option -> unit
end
