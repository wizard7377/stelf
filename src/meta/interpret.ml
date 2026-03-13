(* # 1 "src/meta/interpret.sig.ml" *)
open! Basis
open Funsyn

(* Operational semantics *)
(* Author: Carsten Schuermann *)
module type Interpreter = sig
  (*! structure FunSyn : FUNSYN !*)
  val run : FunSyn.pro_ -> FunSyn.pro_
end
(* Signature Interpreter *)

(* # 1 "src/meta/interpret.fun.ml" *)

(* # 1 "src/meta/interpret.sml.ml" *)
