open! Basis
open Metasyn

(* Basic search engine *)
(* Author: Carsten Schuermann *)
module type OLDSEARCH = sig
  module MetaSyn : METASYN

  exception Error of string

  val searchEx :
    IntSyn.dctx
    * IntSyn.exp_ list
    * (IntSyn.exp_ * IntSyn.sub_)
    * (unit -> MetaSyn.state_) ->
    MetaSyn.state_ list

  val searchAll :
    IntSyn.dctx
    * IntSyn.exp_ list
    * (IntSyn.exp_ * IntSyn.sub_)
    * (MetaSyn.state_ list -> MetaSyn.state_ list) ->
    MetaSyn.state_ list
end
(* signature SEARCH *)
