open Basis
module type SML_OF_NJ = sig 
  (*
  module Cont : CONT
  module IntervalTimer : INTERVAL_TIMER
  module Internals : INTERNALS
  module SysInfo : SYS_INFO
  module Susp : SUSP
  module Weak : WEAK
  *)
  val exportML : string -> bool
  val exportFn : (string * ((string * string list) -> OS.Process.status)) -> unit
  val getCmdName : unit -> string
  val getArgs : unit -> string list
  val getAllArgs : unit -> string list
  type 'a frag
    = QUOTE of string
    | ANTIQUOTE of 'a
  val exnHistory : exn -> string list 
end 