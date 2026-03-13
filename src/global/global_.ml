(* # 1 "src/global/global_.sig.ml" *)
open! Basis

(* Global parameters *)
(* Author: Frank Pfenning *)
module type GLOBAL = sig
  val chatter : int ref
  val style : int ref
  val maxCid : int
  val maxMid : int
  val maxCSid : int
  val doubleCheck : bool ref
  val unsafe : bool ref
  val autoFreeze : bool ref
  val chPrint : int -> (unit -> string) -> unit
  val chMessage : int -> (unit -> string) -> (string -> unit) -> unit
  val timeLimit : Time.time option ref
end

(* in seconds *)
(* signature GLOBAL *)

(* # 1 "src/global/global_.fun.ml" *)

(* # 1 "src/global/global_.sml.ml" *)
open! Basis

(* Global parameters *)
(* Author: Frank Pfenning *)
module Global : GLOBAL = struct
  let chatter = ref 3
  let style = ref 0
  let maxCid = 19999
  let maxMid = 999
  let maxCSid = 49
  let doubleCheck = ref false
  let unsafe = ref false
  let autoFreeze = ref true

  (* !!!reconsider later!!! Thu Mar 10 09:42:28 2005 *)
  let timeLimit = ref (None : Time.time option)

  let rec chPrint n s =
    begin if !chatter >= n then print (s ()) else ()
    end

  let rec chMessage n s f =
    begin if !chatter >= n then f (s ()) else ()
    end
end
(* structure Global *)
