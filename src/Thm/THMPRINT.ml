(* # 1 "src/thm/Thmprint.sig.ml" *)
open! Basis
open Thmsyn

(* Printer for Meta Theorems *)
(* Author: Carsten Schuermann *)

module type THMPRINT = sig
  module ThmSyn : THMSYN

  val tDeclToString : ThmSyn.tDecl -> string
  val callpatsToString : ThmSyn.callpats -> string
  val rDeclToString : ThmSyn.rDecl -> string

  (* -bp *)
  val rOrderToString : ThmSyn.redOrder -> string

  (* -bp *)
  val tabledDeclToString : ThmSyn.tabledDecl -> string

  (* -bp *)
  val keepTableDeclToString : ThmSyn.keepTableDecl -> string
end
