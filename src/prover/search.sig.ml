open! Basis

(* Basic search engine: Version 1.3*)
(* Author: Carsten Schuermann *)
module type SEARCH = sig
  (*! structure IntSyn   : INTSYN !*)
  (*! structure Tomega   : TOMEGA !*)
  module State : State.STATE

  exception Error of string

  val searchEx :
    int * IntSyn.exp_ list * (int -> unit) ->
    unit (*      * (StateSyn.FunSyn.IntSyn.Exp * StateSyn.FunSyn.IntSyn.Sub) *)
end
(* signature SEARCH *)
