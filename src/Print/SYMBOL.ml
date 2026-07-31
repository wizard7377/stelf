open! Basis
open! Global
open! Global.Global_
open! Intsyn
open! Intsyn.Lambda_
open! Names
open! Names.Names_
open! Formatter
open! Formatter__Formatter_

(* # 1 "src/print/Symbol.sig.ml" *)
open! Basis

module type SYMBOL = sig
  val str : string -> string * int
  val evar : string -> string * int
  val bvar : string -> string * int
  val const : string -> string * int
  val label : string -> string * int
  val skonst : string -> string * int
  val def : string -> string * int
  val fvar : string -> string * int
  val sym : string -> string * int
end
