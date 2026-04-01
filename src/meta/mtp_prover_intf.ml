(* # 1 "src/meta/prover.sig.ml" *)
open! Basis
open Funsyn
open Statesyn
open Mtp_global
open Mtp_init
open Mtp_strategy
open Relfun

(* Meta Prover Version 1.3 *)
(* Author: Carsten Schuermann *)

module type MTPROVER = sig
  exception Error of string

  val init : int * Lambda.Intsyn.IntSyn.cid list -> unit
  val auto : unit -> unit
  val print : unit -> unit
  val install :
    (Lambda.Intsyn.IntSyn.conDec -> Lambda.Intsyn.IntSyn.cid) -> unit
end
