(* # 1 "src/meta/Strategy.sig.ml" *)
open! Basis
open Funsyn
open Statesyn
open MtpGlobal
open MtpFilling
open MtpData
open MtpSplitting
open MtpRecursion
open Inference
open MtpPrint
open Timers
open TimeLimit

(* MTPStrategy : Version 1.3 *)
(* Author: Carsten Schuermann *)

module type MTPSTRATEGY = sig
  module StateSyn : STATESYN

  val run : StateSyn.state list -> StateSyn.state list * StateSyn.state list
end
