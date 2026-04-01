open Timing_
include module type of Timers_intf

module MakeTimers (Timers__0 : sig
  module Timing' : TIMING
end) : TIMERS

module Timers : TIMERS
