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

(* # 1 "src/modes/Modeprint.sig.ml" *)
open! Basis
open Modesyn

(* Printing Mode Declarations *)
(* Author: Carsten Schuermann *)

module type MODEPRINT = sig
  (*! structure ModeSyn : MODESYN !*)
  val modeToString : IntSyn.cid * ModeSyn.modeSpine -> string
  val modesToString : (IntSyn.cid * ModeSyn.modeSpine) list -> string
end
