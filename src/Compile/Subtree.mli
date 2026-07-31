open! Basis
open! Global
open! Global.Global_
open! Table
open! Table.Table_
open! Intsyn
open! Intsyn.Lambda_
open! Names
open! Names.Names_
open! Print
open! Print.Print_
open! Formatter
open! Formatter__Formatter_
open! Index
open! Index.Index_
open! Typecheck
open! Typecheck.Typecheck_
open! Solvers
open! Solvers.Solvers_
open! Subordinate
open! Subordinate
include module type of SUBTREE

module SubTree (SubTree__0 : sig
  (*! structure IntSyn' : INTSYN !*)
  (*!structure CompSyn' : COMPSYN !*)
  (*!  sharing CompSyn'.IntSyn = IntSyn' !*)
  module Whnf : WHNF

  (*!  sharing Whnf.IntSyn = IntSyn' !*)
  module Unify : UNIFY

  (*!  sharing Unify.IntSyn = IntSyn'!*)
  module Print : PRINT

  (*!  sharing Print.IntSyn = IntSyn' !*)
  (* CPrint currently unused *)
  module CPrint : Cprint.CPRINT

  (*!  sharing CPrint.IntSyn = IntSyn' !*)
  (*!  sharing CPrint.CompSyn = CompSyn' !*)
  (* unused *)
  module Formatter : FORMATTER

  (*!  sharing Print.Formatter = Formatter !*)
  (* unused *)
  module Names : NAMES

  (*!  sharing Names.IntSyn = IntSyn' !*)
  module CsManager : CsManager.CS_MANAGER
end) : SUBTREE
