(* # 1 "src/meta/global.sig.ml" *)
open! Basis
open Meta_global

(* Global parameters *)
(* Author: Carsten Schuermann *)
include Mtp_global_intf
(* signature MTPGLOBAL *)

(* # 1 "src/meta/global.fun.ml" *)
open! Basis

(* Meta Global parameters *)
(* Author: Carsten Schuermann *)
module MTPGlobal (MTPGlobal__0 : sig
  module MetaGlobal : METAGLOBAL
end) : MTPGLOBAL = struct
  type proverType = New | Old [@@deriving eq, ord, show]

  let prover = ref New
  let maxFill = MetaGlobal.maxFill
  let maxSplit = MetaGlobal.maxSplit
  let maxRecurse = MetaGlobal.maxRecurse
end
(* structure MTPGlobal *)

(* # 1 "src/meta/mtp_global.sml.ml" *)
