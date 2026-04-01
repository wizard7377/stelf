(* # 1 "src/meta/data.sig.ml" *)
open! Basis
open Mtp_global

(* Data aquired during proof search *)
(* Author: Carsten Schuermann *)
include Mtp_data_intf
(* signature MTPDATA *)

(* # 1 "src/meta/data.fun.ml" *)
open! Basis

(* Meta Global parameters *)
(* Author: Carsten Schuermann *)
module MTPData (MTPData__0 : sig
  module MTPGlobal : Mtp_global.MTPGLOBAL
end) : Mtp_data_intf.MTPDATA = struct
  let maxFill = ref 0
end
(* structure MTPData*)

(* # 1 "src/meta/mtp_data.sml.ml" *)
