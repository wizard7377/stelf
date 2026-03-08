open! Basis

(* Meta syntax *)
(* Author: Carsten Schuermann *)
module type METASYN = sig
  (*! structure IntSyn : INTSYN !*)
  type mode_ = Bot | Top

  (* Mode                       *)
  (* M ::= Bot                  *)
  (*     | Top                  *)
  type prefix_ = Prefix of IntSyn.dctx * mode_ IntSyn.ctx_ * int IntSyn.ctx_

  (* Mtx modes                  *)
  (* G   declarations           *)

  (* Prefix P := *)
  (* Btx splitting depths       *)
  type state_ = State of string * prefix_ * IntSyn.exp_

  (*             G; Mtx; Btx    *)
  (*             [name]         *)

  (* State S :=                 *)
  (*             |- V           *)
  type sgn_ = SgnEmpty | ConDec of IntSyn.conDec_ * sgn_

  (* Interface signature        *)
  (* IS ::= .                   *)
  (*      | c:V, IS             *)
  val createAtomConst : IntSyn.dctx * IntSyn.head_ -> IntSyn.exp_ * IntSyn.eclo
  val createAtomBVar : IntSyn.dctx * int -> IntSyn.exp_ * IntSyn.eclo
end
(* signature METASYN *)
