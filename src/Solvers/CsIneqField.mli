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

(* # 1 "src/solvers/CsIneqField.sig.ml" *)

(* # 1 "src/solvers/CsIneqField.fun.ml" *)
open! Basis

module CsIneqField (CSIneqField__0 : sig
  (* Solver for a linearly ordered field, based on the simplex method *)
  (* Author: Roberto Virga *)
  module OrderedField : OrderedField.ORDERED_FIELD

  (*! structure IntSyn : INTSYN !*)
  module Trail : TRAIL
  module Unify : UNIFY

  (*! sharing Unify.IntSyn = IntSyn !*)
  module SparseArray : SparseArray.SPARSE_ARRAY
  module SparseArray2 : SparseArray2.SPARSE_ARRAY2

  (*! structure CsManager : CS_MANAGER !*)
  (*! sharing CsManager.IntSyn = IntSyn !*)
  module CsEqField :
    CsEqField.CS_EQ_FIELD with type Field.number = OrderedField.number

  (*! sharing CsEqField.IntSyn = IntSyn !*)
  (*! sharing CsEqField.CsManager = CsManager !*)
end) : Cs.CS
