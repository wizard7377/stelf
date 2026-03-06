open! Basis;;
module type MSG = sig
                  val message : string -> unit
                  val setMessageFunc : (string -> unit) -> unit
                  end;;
module Msg : MSG =
  struct
    let default = print;;
    let messageFunc = ref default;;
    let rec setMessageFunc f = messageFunc := f;;
    let rec message s = ( ! ) messageFunc s;;
    end;;