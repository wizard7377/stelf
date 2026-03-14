(* # 1 "src/timing/timing_.sig.ml" *)

(* # 1 "src/timing/timing_.fun.ml" *)

(* # 1 "src/timing/timing_.sml.ml" *)
open! Basis

(* Timing utilities based on SML'97 Standard Library *)
(* Author: Frank Pfenning *)
(*
   For documentation on timers and time, see also the
   SML'97 Standard Library structures Time and Timer

   In saved heaps in SML of NJ, a global timer must
   be initialized, otherwise exception Time.Time is raised
   somewhere.
*)
module type TIMING = sig
  val init : unit -> unit

  type nonrec center

  val newCenter : string -> center
  val reset : center -> unit
  val time : center -> ('a -> 'b) -> 'a -> 'b

  type nonrec sum

  val sumCenter : string * center list -> sum
  val toString : center -> string
  val sumToString : sum -> string
end

(* signature TIMING *)
module Timing : TIMING = struct
  (* user and system time add up to total CPU time used *)
  (* gc time is a portion of the total CPU time devoted to garbage collection *)
  type nonrec __0 = { usr : Time.time; sys : Time.time; gc : Time.time }
  type nonrec cpuTime = __0
  type nonrec realTime = Time.time

  let init () = ()

  type 'a result = Value of 'a | Exception of exn
  type nonrec center = string * (cpuTime * realTime) ref
  type nonrec sum = string * center list

  let zero = { usr = Time.zeroTime; sys = Time.zeroTime; gc = Time.zeroTime }

  let minus ({ usr = t1; sys = t2; gc = t3 }, { usr = s1; sys = s2; gc = s3 }) =
    { usr = Time.( - ) t1 s1; sys = Time.( - ) t2 s2; gc = Time.( - ) t3 s3 }

  let plus ({ usr = t1; sys = t2; gc = t3 }, { usr = s1; sys = s2; gc = s3 }) =
    { usr = Time.( + ) t1 s1; sys = Time.( + ) t2 s2; gc = Time.( + ) t3 s3 }

  let sum { usr = t1; sys = t2; gc = _t3 } = Time.( + ) t1 t2

  open! struct end

  (* We use only one global timer each for CPU time and real time *)
  (* val CPUTimer = Timer.startCPUTimer () *)
  (* val realTimer = Timer.startRealTimer () *)
  (* newCenter (name) = new center, initialized to 0 *)
  let newCenter name = (name, ref (zero, Time.zeroTime))

  (* reset (center) = (), reset center to 0 as effect *)
  let reset (_, counters) = counters := (zero, Time.zeroTime)

  (* time center f x = y
       runs f on x and adds its time to center.
       If f x raises an exception, this is properly re-raised

       Warning: if the execution of f uses its own centers,
       the time for those will be counted twice!
    *)
  (* TODO: Timer module is not directly accessible via open Basis.
       Stub the timer-dependent functions until Timer is properly available. *)
  let checkCPUAndGCTimer _timer = zero

  let time (_, _counters) (f : 'a -> 'b) (x : 'a) =
    let result = try Value (f x) with exn -> Exception exn in
    begin match result with Value v -> v | Exception e -> raise e
    end

  (* sumCenter (name, centers) = sc
       where sc is a new sum which contains the sum of the timings of centers.

       Warning: the centers should not overlap!
    *)
  let sumCenter (name, l) = (name, l)
  let stdTime (n, time) = StringCvt.padLeft ' ' n (Time.toString time)

  let timesToString
      (name, (({ usr = t1; sys = _t2; gc = t3 } as cPUTime_), realTime)) =
    ((((((((((((name ^ ": ") ^ "Real = ") ^ stdTime (7, realTime)) ^ ", ")
           ^ "Run = ")
          ^ stdTime (7, sum cPUTime_))
         ^ " ")
        ^ "(")
       ^ stdTime (7, t1))
      ^ " usr, ")
     ^ stdTime (6, t3))
    ^ " gc)")
    ^ "\n"
  (* ^ stdTime (5, t2) ^ "" sys, "" ^ *)
  (* elide sys time *)

  let toString (name, { contents = cPUTime_, realTime }) =
    timesToString (name, (cPUTime_, realTime))

  let sumToString (name, centers) =
    let rec sumup = function
      | [], (cPUTime_, realTime) -> timesToString (name, (cPUTime_, realTime))
      | (_, { contents = c_, r_ }) :: centers, (cPUTime_, realTime) ->
          sumup (centers, (plus (cPUTime_, c_), Time.( + ) realTime r_))
    in
    sumup (centers, (zero, Time.zeroTime))
end

(* local ... *)
(* structure Timing *)
(* This version only counts, but does not time *)
(* Unused in the default linking, but could be *)
(* passed as a paramter to Timers *)
module Counting : TIMING = struct
  type 'a result = Value of 'a | Exception of exn
  type nonrec center = string * int ref
  type nonrec sum = string * center list

  let init () = ()
  let newCenter name = (name, ref 0)
  let reset (_, counters) = counters := 0

  let time (_, counters) (f : 'a -> 'b) (x : 'a) =
    let _ = counters := !counters + 1 in
    f x

  let sumCenter (name, l) = (name, l)
  let toString' (name, n) = ((name ^ ": ") ^ Int.toString n) ^ "\n"
  let toString (name, { contents = n }) = toString' (name, n)

  let sumToString (name, centers) =
    let rec sumup = function
      | [], total -> toString' (name, total)
      | (_, { contents = n }) :: centers, total -> sumup (centers, total + n)
    in
    sumup (centers, 0)
end
(* structure Counting *)
