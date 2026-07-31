open! Basis
open! Trail
open! Trail.Trail_
open! Global
open! Global.Global_
open! Domains
open! Domains.Domains_
open! Intsyn
open! Intsyn.Lambda_
open! Names
open! Names.Names_
open! Modes
open! Modes.Modes_
open! Table
open! Table.Table_
open! Print
open! Print.Print_
open! Formatter
open! Formatter__Formatter_

(* # 1 "src/solvers/CsIntegersWord.sig.ml" *)

(* # 1 "src/solvers/CsIntegersWord.fun.ml" *)
open! Basis

module Cs_int_word (CSIntWord__0 : sig
  (* Solver for machine integers *)
  (* Author: Roberto Virga *)
  (*! structure IntSyn : INTSYN !*)
  module Whnf : WHNF

  (*! sharing Whnf.IntSyn = IntSyn !*)
  module Unify : UNIFY

  (*! sharing Unify.IntSyn = IntSyn !*)
  (*! structure CsManager : CS_MANAGER !*)
  (*! sharing CsManager.IntSyn = IntSyn !*)
  val wordSize : int
end) : Cs.CS
