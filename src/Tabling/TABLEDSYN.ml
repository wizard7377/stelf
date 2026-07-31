open! Basis
open! Table
open! Table.Table_
open! Intsyn
open! Intsyn.Lambda_
open! Print
open! Print.Print_
open! Names
open! Names.Names_
open! Paths
open! Paths.Paths_
open! Index
open! Index.Index_

(* # 1 "src/tabling/Tabledsyn.sig.ml" *)
open! Basis

(* Tabled Syntax *)
(* Author: Brigitte Pientka *)

module type TABLEDSYN = sig
  (*! structure IntSyn : INTSYN !*)
  exception Error of string

  val reset : unit -> unit
  val installTabled : IntSyn.cid -> unit
  val installKeepTable : IntSyn.cid -> unit
  val tabledLookup : IntSyn.cid -> bool
  val keepTable : IntSyn.cid -> bool
end
