(* # 1 "src/timing/timers.sig.ml" *)
open Basis
open Timing_
module Timing = Timing_.Timing

(* Timers collecting statistics about Stelf *)
(* Author: Frank Pfenning *)
include Timers_intf
(* check, then reset *)
(* signature TIMERS *)

(* # 1 "src/timing/timers.fun.ml" *)
open! Timing_

(* Timers collecting statistics about Stelf *)
(* Author: Frank Pfenning *)
module MakeTimers (Timers__0 : sig
  module Timing' : TIMING
end) : TIMERS = struct
  open Timers__0
  module Timing = Timing'

  let parsing = Timing.newCenter "Parsing       "
  let recon = Timing.newCenter "Reconstruction"
  let abstract = Timing.newCenter "Abstraction   "
  let checking = Timing.newCenter "Checking      "
  let modes = Timing.newCenter "Modes         "
  let subordinate = Timing.newCenter "Subordination "
  let terminate = Timing.newCenter "Termination   "
  let printing = Timing.newCenter "Printing      "
  let compiling = Timing.newCenter "Compiling     "
  let solving = Timing.newCenter "Solving       "
  let coverage = Timing.newCenter "Coverage      "
  let worlds = Timing.newCenter "Worlds        "
  let ptrecon = Timing.newCenter "ProofRecon    "
  let filling = Timing.newCenter "Filling       "
  let filltabled = Timing.newCenter "Filling Tabled"
  let splitting = Timing.newCenter "Splitting     "
  let recursion = Timing.newCenter "Recursion     "
  let inference = Timing.newCenter "Inference     "
  let delphin = Timing.newCenter "Delphin       "

  let centers =
    [
      parsing;
      recon;
      abstract;
      checking;
      modes;
      subordinate;
      terminate;
      printing;
      compiling;
      solving;
      coverage;
      worlds;
      ptrecon;
      filling;
      filltabled;
      splitting;
      recursion;
      inference;
      delphin;
    ]

  let total = Timing.sumCenter ("Total         ", centers)
  let time = Timing.time
  let reset () = List.app Timing.reset centers

  let check () =
    begin
      List.app (fun x -> print (Timing.toString x)) centers;
      begin
        print (Timing.sumToString total);
        print "Remember that the success continuation counts into Solving!\n"
      end
    end

  let show () =
    begin
      check ();
      reset ()
    end
end
(* functor Timers *)

(* # 1 "src/timing/timers.sml.ml" *)

(* Timers *)
(* Author: Frank Pfenning *)
module Timers = MakeTimers (struct
  module Timing' = Timing
end)
(*
 alternative not using actual timers 
structure Timers =
  Timers (structure Timing' = Counting);
*)
