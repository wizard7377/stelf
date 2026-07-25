(* # 1 "src/m2/Metasyn.sig.ml" *)
open! Basis

(* Meta syntax *)
(* Author: Carsten Schuermann *)

module type METASYN = sig
  (*! structure IntSyn : INTSYN !*)
  type mode = Bot | Top [@@deriving eq, ord, show]

  (* Mode                       *)
  (* M ::= Bot                  *)
  (*     | Top                  *)
  type prefix = Prefix of IntSyn.dctx * mode IntSyn.ctx * int IntSyn.ctx

  (* Mtx modes                  *)
  (* G   declarations           *)

  (* Prefix P := *)
  (* Btx splitting depths       *)
  type state = State of string * prefix * IntSyn.exp

  (*             G; Mtx; Btx    *)
  (*             [name]         *)

  (* State S :=                 *)
  (*             |- V           *)
  type sgn = SgnEmpty | ConDec of IntSyn.conDec * sgn

  (* Interface signature        *)
  (* IS ::= .                   *)
  (*      | c:V, IS             *)
  val createAtomConst : IntSyn.dctx * IntSyn.head -> IntSyn.exp * IntSyn.eclo
  val createAtomBVar : IntSyn.dctx * int -> IntSyn.exp * IntSyn.eclo
end
