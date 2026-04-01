(* # 1 "src/m2/search.sig.ml" *)
open! Basis
open Metasyn

(* Basic search engine *)
(* Author: Carsten Schuermann *)

module type OLDSEARCH = sig
  module MetaSyn : Metasyn.METASYN

  exception Error of string

  val searchEx :
    IntSyn.dctx
    * IntSyn.exp list
    * (IntSyn.exp * IntSyn.sub)
    * (unit -> MetaSyn.state) ->
    MetaSyn.state list

  val searchAll :
    IntSyn.dctx
    * IntSyn.exp list
    * (IntSyn.exp * IntSyn.sub)
    * (MetaSyn.state list -> MetaSyn.state list) ->
    MetaSyn.state list
end
