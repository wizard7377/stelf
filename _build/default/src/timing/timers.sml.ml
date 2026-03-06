open! Basis;;
(* Timers *);;
(* Author: Frank Pfenning *);;
module Timers = (Timers)(struct
                           module Timing' = Timing;;
                           end);;
(*
 alternative not using actual timers 
structure Timers =
  Timers (structure Timing' = Counting);
*);;