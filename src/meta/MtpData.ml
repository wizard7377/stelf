(* # 1 "src/meta/Data.sig.ml" *)
open! Basis
open MtpGlobal

(* Data aquired during proof search *)
(* Author: Carsten Schuermann *)
include MtpData_intf
(* signature MTPDATA *)

(* # 1 "src/meta/Data.fun.ml" *)
open! Basis

(* Meta Global parameters *)
(* Author: Carsten Schuermann *)
module MTPData (MTPData__0 : sig
  module MTPGlobal : MtpGlobal.MTPGLOBAL
end) : MtpData_intf.MTPDATA = struct
  let maxFill = ref 0
end
(* structure MTPData*)

(* # 1 "src/meta/MtpData.sml.ml" *)
