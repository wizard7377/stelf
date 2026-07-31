open! Basis
open! Stream
open! Stream.Stream_
open! Global
open! Global.Global_
open! Intsyn
open! Intsyn.Lambda_
open! Names
open! Names.Names_
open! Modes
open! Modes.Modes_
open! Paths
open! Paths.Paths_
open! Formatter
open! Formatter__Formatter_
open! Print
open! Print.Print_
open! Typecheck
open! Typecheck.Typecheck_
open! Terminate
open! Terminate.Terminate_
open! Index
open! Index.Index_
open! Thm
open! Thm.Thm_
open! Opsem
open! Opsem.Opsem_
open! Compile
open! Compile.Compile_
open! Subordinate
open! Subordinate
open! Table
open! Table.Table_
open! Timing
open! Timing.Timing_
open! Solvers
open! Solvers.Solvers_

(* # 1 "src/m2/Search.sig.ml" *)
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
