(* # 1 "src/opsem/absmachine_sbt.sig.ml" *)
open! Basis

(* Abstract Machine *)
(* Author: Iliano Cervesato *)
(* Modified: Jeff Polakow *)
(* Modified: Frank Pfenning *)

module type ABSMACHINESBT = sig
  (*! structure IntSyn  : INTSYN !*)
  (*! structure CompSyn : COMPSYN !*)
  val solve :
    (CompSyn.goal * IntSyn.sub)
    * CompSyn.dProg
    * (CompSyn.flatterm list -> unit) ->
    unit
end
