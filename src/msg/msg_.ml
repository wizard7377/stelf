(* # 1 "src/msg/msg_.sig.ml" *)

(* # 1 "src/msg/msg_.fun.ml" *)

(* # 1 "src/msg/msg_.sml.ml" *)
open! Basis

module type MSG = sig
  val message : string -> unit
  val setMessageFunc : (string -> unit) -> unit
end

module Msg : MSG = struct
  let default = print
  let messageFunc = ref default
  let setMessageFunc f = messageFunc := f
  let message s = ( ! ) messageFunc s
end
