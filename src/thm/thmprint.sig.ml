open! Basis
open Thmsyn

(* Printer for Meta Theorems *)
(* Author: Carsten Schuermann *)
module type THMPRINT = sig
  module ThmSyn : THMSYN

  val tDeclToString : ThmSyn.tDecl_ -> string
  val callpatsToString : ThmSyn.callpats_ -> string
  val rDeclToString : ThmSyn.rDecl_ -> string

  (* -bp *)
  val rOrderToString : ThmSyn.redOrder_ -> string

  (* -bp *)
  val tabledDeclToString : ThmSyn.tabledDecl_ -> string

  (* -bp *)
  val keepTableDeclToString : ThmSyn.keepTableDecl_ -> string
end
(* -bp *)
(* signature THMPRINT *)
