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
include module type of COMPSYN

module Make_CompSyn
    (Global_ : GLOBAL)
    (Names_ : NAMES)
    (Table_ : TABLE with type key = int) : COMPSYN

module CompSyn : COMPSYN
include COMPSYN
