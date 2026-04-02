(* # 1 "src/opsem/Absmachine.sig.ml" *)
open! Basis

(* Abstract Machine *)
(* Author: Iliano Cervesato *)
(* Modified: Jeff Polakow *)
(* Modified: Frank Pfenning *)

module type ABSMACHINE = sig
  (*! structure IntSyn : INTSYN !*)
  (*! structure CompSyn : COMPSYN !*)
  val solve :
    (CompSyn.goal * IntSyn.sub) * CompSyn.dProg * (IntSyn.exp -> unit) -> unit
end
