open! Basis
open! Global
open! Global.Global_
open! Table
open! Table.Table_
open! Intsyn
open! Intsyn.Lambda_
open! Names
open! Names.Names_

(* # 1 "src/subordinate/Intset.sig.ml" *)

(* # 1 "src/subordinate/Intset.fun.ml" *)

(* # 1 "src/subordinate/Intset.sml.ml" *)
open! Basis

(* Persistent red/black trees *)
(* Specialized for subordination *)
(* Author: Frank Pfenning *)
(* Copied from src/table/red-black-tree.fun *)

module type INTSET = sig
  type intset

  val empty : intset
  val insert : int -> intset -> intset
  val member : int -> intset -> bool
  val foldl : (int * 'b -> 'b) -> 'b -> intset -> 'b
end
