(* # 1 "src/meta/Search.sig.ml" *)
open! Basis
open Funsyn
open Statesyn
open MtpGlobal

(* Basic search engine: Version 1.3*)
(* Author: Carsten Schuermann *)

module type MTPSEARCH = sig
  module StateSyn : STATESYN

  exception Error of string

  val searchEx :
    int * IntSyn.exp list * (int -> unit) ->
    unit (*      * (IntSyn.Exp * IntSyn.Sub) *)
end
