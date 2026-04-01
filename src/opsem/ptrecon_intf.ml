(* # 1 "src/opsem/ptrecon.sig.ml" *)
open! Basis

(* Abstract Machine guided by proof skeleton *)
(* Author: Brigitte Pientks *)
(* Modified: Jeff Polakow *)
(* Modified: Frank Pfenning *)
(* Proof term reconstruction by proof skeleton *)

module type PTRECON = sig
  (*! structure IntSyn : INTSYN !*)
  (*! structure CompSyn : COMPSYN !*)
  exception Error of string

  val solve :
    CompSyn.pskeleton
    * (CompSyn.goal * IntSyn.sub)
    * CompSyn.dProg
    * (CompSyn.pskeleton * IntSyn.exp -> unit) ->
    unit
end
