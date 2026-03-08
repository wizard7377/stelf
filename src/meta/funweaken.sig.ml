open! Basis

(* Weakening substitutions for meta substitutions *)
(* Author: Carsten Schuermann *)
module type FUNWEAKEN = sig
  (*! structure FunSyn : FUNSYN !*)
  val strengthenPsi : FunSyn.lfctx * IntSyn.sub_ -> FunSyn.lfctx * IntSyn.sub_

  val strengthenPsi' :
    FunSyn.lFDec_ list * IntSyn.sub_ -> FunSyn.lFDec_ list * IntSyn.sub_
end
(* signature FUNWEAKEN *)
