(* # 1 "src/msg/Msg_.sig.ml" *)

(* # 1 "src/msg/Msg_.fun.ml" *)

(* # 1 "src/msg/Msg_.sml.ml" *)

open Basis
include Msg_intf
module Msg : MSG = struct
  let default = print
  let messageFunc = ref default
  let setMessageFunc f = messageFunc := f
  let message s = ( ! ) messageFunc s
end
