open! Basis
open! Global
open! Global.Global_
open! Table
open! Table.Table_
open! Intsyn
open! Intsyn.Lambda_
open! Formatter
open! Formatter__Formatter_
open! Print
open! Print.Print_
open! Names
open! Names.Names_
open! Paths
open! Paths.Paths_
open! Index
open! Index.Index_

(* # 1 "src/style/Style_.sig.ml" *)
open! Basis

(* Style Checking *)

(** Author: Carsten Schuermann *)

module type STYLECHECK = sig
  exception Error of string

  val check : unit -> unit

  val checkConDec : IntSyn.cid -> unit
  (** raises Error (msg) *)
end
