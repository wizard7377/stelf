open! Basis
open! Timing
open! Timing.Timing_
open! Frontend
open! Frontend.Frontend_
open! Smlofnj

(* # 1 "src/server/Sigint.sig.ml" *)
open! Basis

module type SIGINT = sig
  val interruptLoop : (unit -> unit) -> unit
end
