open! Basis
open Funsyn
open Statesyn
open Mtp_global
open Mtp_filling
open Mtp_data
open Mtp_splitting
open Mtp_recursion
open Inference
open Mtp_print
open Timers
open Time_limit

(* MTPStrategy : Version 1.3 *)
(* Author: Carsten Schuermann *)
module type MTPSTRATEGY = sig
  module StateSyn : STATESYN

  val run : StateSyn.state_ list -> StateSyn.state_ list * StateSyn.state_ list
end
(* open cases -> remaining cases * solved cases *)
(* signature MTPSTRATEGY *)
