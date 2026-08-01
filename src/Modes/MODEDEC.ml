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

(* # 1 "src/modes/Modedec.sig.ml" *)
open! Basis
open Modesyn

(* Modes: short and long forms *)
(* Author: Carsten Schuermann *)
(* Modified: Frank Pfenning *)

module type MODEDEC = sig
  exception Error of string

  val shortToFull :
    IntSyn.cid -> ModeSyn.modeSpine -> Paths.region -> ModeSyn.modeSpine

  val checkFull : IntSyn.cid -> ModeSyn.modeSpine -> Paths.region -> unit
  val checkPure : IntSyn.cid * ModeSyn.modeSpine -> Paths.region -> unit
end
