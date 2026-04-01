(* # 1 "src/msg/msg_.sig.ml" *)

(* # 1 "src/msg/msg_.fun.ml" *)

(* # 1 "src/msg/msg_.sml.ml" *)

open Basis

module type MSG = sig
  val message : string -> unit
  val setMessageFunc : (string -> unit) -> unit
end
