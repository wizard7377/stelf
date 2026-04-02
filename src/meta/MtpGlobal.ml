(* # 1 "src/meta/Global.sig.ml" *)
open! Basis
open MetaGlobal

(* Global parameters *)
(* Author: Carsten Schuermann *)
include MtpGlobal_intf
(* signature MTPGLOBAL *)

(* # 1 "src/meta/Global.fun.ml" *)
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

(* # 1 "src/meta/MtpGlobal.sml.ml" *)
