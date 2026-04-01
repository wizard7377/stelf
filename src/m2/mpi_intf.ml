(* # 1 "src/m2/mpi.sig.ml" *)
open! Basis
open Metasyn

(* Meta Prover Interface *)
(* Author: Carsten Schuermann *)

module type MPI = sig
  module MetaSyn : Metasyn.METASYN

  exception Error of string

  val init : int * string list -> unit
  val select : int -> unit
  val print : unit -> unit
  val next : unit -> unit
  val auto : unit -> unit
  val solve : unit -> unit
  val lemma : string -> unit
  val reset : unit -> unit
  val extract : unit -> MetaSyn.sgn
  val show : unit -> unit
  val undo : unit -> unit
end
