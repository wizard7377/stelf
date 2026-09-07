
(* # 1 "src/meta/Interpret.sig.ml" *)
open Funsyn

(* Operational semantics *)
(* Author: Carsten Schuermann *)

module type Interpreter = sig
  (*! structure FunSyn : FUNSYN !*)
  val run : FunSyn.pro -> FunSyn.pro
end
