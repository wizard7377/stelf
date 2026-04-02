(* # 1 "src/msg/Msg_.sig.ml" *)

(* # 1 "src/msg/Msg_.fun.ml" *)

(* # 1 "src/msg/Msg_.sml.ml" *)

open Basis

module type MSG = sig
  val message : string -> unit
  val setMessageFunc : (string -> unit) -> unit
end
