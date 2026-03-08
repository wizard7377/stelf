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
    * (CompSyn.goal_ * IntSyn.sub_)
    * CompSyn.dProg_
    * (CompSyn.pskeleton * IntSyn.exp_ -> unit) ->
    unit
end
(* signature PTRECON *)
