open Timing_
include module type of Timers_intf

module MakeTimers (Timing' : TIMING) : TIMERS with module Timing = Timing'

module Timers : TIMERS
