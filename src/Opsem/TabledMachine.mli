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
open! Compile
open! Compile.Compile_
open! CompSyn
open! Assign
open! Tabling
include module type of TABLEDMACHINE

module Tabled (Tabled__0 : sig
  (*! structure IntSyn' : INTSYN !*)
  (*! structure CompSyn' : COMPSYN !*)
  (*! sharing CompSyn'.IntSyn = IntSyn' !*)
  module Unify : UNIFY

  (*! sharing Unify.IntSyn = IntSyn' !*)
  module TabledSyn : Tabledsyn.TABLEDSYN

  (*!  sharing TabledSyn.IntSyn = IntSyn' !*)
  module Assign : ASSIGN

  (*!  sharing Assign.IntSyn = IntSyn' !*)
  module Index : INDEX

  (*!  sharing Index.IntSyn = IntSyn' !*)
  module Queue : Queue.QUEUE

  (*! structure TableParam : TABLEPARAM !*)
  (*!  sharing TableParam.IntSyn = IntSyn' !*)
  (*!  sharing TableParam.CompSyn = CompSyn' !*)
  module AbstractTabled : ABSTRACTTABLED.ABSTRACTTABLED

  (*!  sharing AbstractTabled.IntSyn = IntSyn' !*)
  (*! sharing AbstractTabled.TableParam = TableParam !*)
  module MemoTable : MEMOTABLE.MEMOTABLE

  (*!  sharing MemoTable.IntSyn = IntSyn' !*)
  (*!  sharing MemoTable.CompSyn = CompSyn'  !*)
  (*! sharing MemoTable.TableParam = TableParam  !*)
  (* CPrint currently unused *)
  module CPrint : Cprint.CPRINT

  (*!  sharing CPrint.IntSyn = IntSyn' !*)
  (*!  sharing CPrint.CompSyn = CompSyn' !*)
  (* CPrint currently unused *)
  module Print : PRINT
end) : TABLEDMACHINE.TABLED
