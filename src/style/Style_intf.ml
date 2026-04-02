(* # 1 "src/style/Style_.sig.ml" *)
open! Basis

(* Style Checking *)

(** Author: Carsten Schuermann *)

module type STYLECHECK = sig
  exception Error of string

  val check : unit -> unit

  val checkConDec : IntSyn.cid -> unit
  (** raises Error (msg) *)
end
