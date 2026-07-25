(* # 1 "src/msg/Msg_.sig.ml" *)

(* # 1 "src/msg/Msg_.fun.ml" *)

(* # 1 "src/msg/Msg_.sml.ml" *)

open Basis
include MSG

module Msg : MSG = struct
  let default m = Display.debug (Display.string m)
  let messageFunc = ref default
  let setMessageFunc f = messageFunc := f
  let message s = ( ! ) messageFunc s
end
