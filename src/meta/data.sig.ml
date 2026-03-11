open! Basis
open Mtp_global

(* Data aquired during proof search *)
(* Author: Carsten Schuermann *)
module type MTPDATA = sig
  val maxFill : int ref
end
(* signature MTPDATA *)
