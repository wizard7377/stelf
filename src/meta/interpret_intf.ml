(* # 1 "src/meta/interpret.sig.ml" *)
open! Basis
open Funsyn

(* Operational semantics *)
(* Author: Carsten Schuermann *)

module type Interpreter = sig
  (*! structure FunSyn : FUNSYN !*)
  val run : FunSyn.pro -> FunSyn.pro
end
