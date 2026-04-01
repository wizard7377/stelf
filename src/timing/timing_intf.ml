open Basis

(* Timing utilities based on SML'97 Standard Library *)
(* Author: Frank Pfenning *)
module type TIMING = sig
  val init : unit -> unit

  type center

  val newCenter : string -> center
  val reset : center -> unit
  val time : center -> ('a -> 'b) -> 'a -> 'b

  type sum

  val sumCenter : string * center list -> sum
  val toString : center -> string
  val sumToString : sum -> string
end
