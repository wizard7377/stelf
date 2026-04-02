(* # 1 "src/opsem/AbstractTabled.sig.ml" *)
open! Basis
open TableParam

(* Abstraction *)
(* Author: Brigitte Pientka *)

module type ABSTRACTTABLED = sig
  (*! structure IntSyn : INTSYN !*)
  (*! structure TableParam : TABLEPARAM !*)
  exception Error of string

  val abstractEVarCtx :
    CompSyn.dProg * IntSyn.exp * IntSyn.sub ->
    IntSyn.dctx
    * IntSyn.dctx
    * IntSyn.dctx
    * IntSyn.exp
    * TableParam.resEqn
    * IntSyn.sub

  val abstractAnswSub : IntSyn.sub -> IntSyn.dctx * IntSyn.sub
  val raiseType : IntSyn.dctx * IntSyn.exp -> IntSyn.exp
end
