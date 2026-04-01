(* # 1 "src/print/print_twega.sig.ml" *)
open! Basis

(* Printing Signatures *)
(* Author: Frank Pfenning *)

module type PRINT_TWEGA = sig
  val printSgn : unit -> unit
  val printSgnToFile : string -> unit
end
