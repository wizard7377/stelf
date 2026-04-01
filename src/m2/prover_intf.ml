(* # 1 "src/m2/prover.sig.ml" *)
open! Basis

(* Meta Prover *)
(* Author: Carsten Schuermann *)

module type PROVER = sig
  (*! structure IntSyn : INTSYN !*)
  exception Error of string

  val init : int * IntSyn.cid list -> unit
  val auto : unit -> unit
  val print : unit -> unit
  val install : (IntSyn.conDec -> IntSyn.cid) -> unit
end
