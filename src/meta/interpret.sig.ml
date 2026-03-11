open! Basis
open Funsyn

(* Operational semantics *)
(* Author: Carsten Schuermann *)
module type Interpreter = sig
  (*! structure FunSyn : FUNSYN !*)
  val run : FunSyn.pro_ -> FunSyn.pro_
end
(* Signature Interpreter *)
