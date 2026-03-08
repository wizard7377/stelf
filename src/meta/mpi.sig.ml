open! Basis

(* Meta Prover Interface *)
(* Author: Carsten Schuermann *)
module type MTPI = sig
  (*! structure FunSyn : FUNSYN !*)
  module StateSyn : STATESYN

  exception Error of string

  val init : int * string list -> unit
  val select : int -> unit
  val print : unit -> unit
  val next : unit -> unit
  val auto : unit -> unit
  val solve : unit -> unit
  val check : unit -> unit
  val reset : unit -> unit

  (*  val extract: unit -> MetaSyn.Sgn *)
  (*  val show   : unit -> unit *)
  val undo : unit -> unit
end
(* signature MTPI *)
