(* # 1 "src/msg/msg_.sig.ml" *)

(* # 1 "src/msg/msg_.fun.ml" *)

(* # 1 "src/msg/msg_.sml.ml" *)

open Basis
include Msg_intf
module Msg : MSG = struct
  let default = print
  let messageFunc = ref default
  let setMessageFunc f = messageFunc := f
  let message s = ( ! ) messageFunc s
end
