(* # 1 "src/global/Global_.sig.ml" *)

open Basis

(* Global parameters *)

include GLOBAL
(** Author: Frank Pfenning *)

(* in seconds *)
(* signature GLOBAL *)

(* # 1 "src/global/Global_.fun.ml" *)

(* # 1 "src/global/Global_.sml.ml" *)

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

  let arrow_reserved = ref false
  let arrow_infix = ref false
  let latin_uppercase = ref false
  let bar_in_block = ref false
  let old_some = ref false
  let stop_reserved = ref false
end
(* structure Global *)
