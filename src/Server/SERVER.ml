open! Basis
open! Timing
open! Timing.Timing_
open! Frontend
open! Frontend.Frontend_
open! Smlofnj

(* # 1 "src/server/Server_.sig.ml" *)

(* # 1 "src/server/Server_.fun.ml" *)

(* # 1 "src/server/Server_.sml.ml" *)
open! Basis

(** Interactive command server for Stelf/STELF. *)

module type SERVER = sig
  val server : string -> string list -> OS.Process.status
end
