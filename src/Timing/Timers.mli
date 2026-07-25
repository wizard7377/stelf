open Timing_
include module type of TIMERS
module MakeTimers (Timing' : TIMING) : TIMERS with module Timing = Timing'
module Timers : TIMERS
