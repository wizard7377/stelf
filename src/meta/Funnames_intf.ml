(* # 1 "src/meta/Funnames.sig.ml" *)
open! Basis
open Funsyn

(* Names of Constants and Variables *)
(* Author: Carsten Schuermann *)

module type FUNNAMES = sig
  (*! structure FunSyn : FUNSYN !*)
  exception Error of string

  (* Constant names and fixities *)
  val reset : unit -> unit
  val installName : string * FunSyn.lemma -> unit
  val nameLookup : string -> FunSyn.lemma option
  val constName : FunSyn.lemma -> string
end
