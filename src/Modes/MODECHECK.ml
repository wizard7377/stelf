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

(* # 1 "src/modes/Modecheck.sig.ml" *)
open! Basis
open Modesyn

(* Mode Checking *)
(* Author: Carsten Schuermann *)
(* Modified: Frank Pfenning *)

module type MODECHECK = sig
  exception Error of string

  (* for new declarations *)
  val checkD : IntSyn.conDec * string * Paths.occConDec option -> unit

  (* raises Error (msg) *)
  (* for prior declarations *)
  val checkMode : IntSyn.cid * ModeSyn.modeSpine -> unit

  (* raises Error(msg) *)
  (* for output coverage of prior declarations *)
  val checkFreeOut : IntSyn.cid * ModeSyn.modeSpine -> unit
end
