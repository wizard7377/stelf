(* # 1 "src/opsem/opsem_.sig.ml" *)

(* # 1 "src/opsem/opsem_.fun.ml" *)

(* # 1 "src/opsem/opsem_.sml.ml" *)
open! Basis
module TabledSyn = Tabled.TabledSyn

module AbsMachine = Absmachine.AbsMachine (struct
  (*! structure IntSyn' = IntSyn !*)
  (*! structure CompSyn' = CompSyn !*)
  module Unify = UnifyTrail
  module Assign = Assign__
  module Index = Index
  module CPrint = CPrint
  module Print = Print
  module Names = Names
end)

(*! structure Cs_manager = Cs_manager !*)
module AbstractTabled = Abstract_tabled.AbstractTabled (struct
  (*! structure IntSyn' = IntSyn !*)
  module Print = Print
  module Whnf = Whnf
  module Unify = UnifyTrail
  module Constraints = Constraints
  module Subordinate = Subordinate.Subordinate_.Subordinate

  (*! structure TableParam = TableParam !*)
  module Conv = Conv
end)

module MemoTable = Memo_table.MemoTable (struct
  (*! structure IntSyn' = IntSyn !*)
  (*! structure CompSyn' = CompSyn !*)
  module Conv = Conv
  module Whnf = Whnf
  module Print = Print

  (*! structure TableParam = TableParam !*)
  module AbstractTabled = AbstractTabled
  module Table = IntRedBlackTree
end)

(*! structure RBSet = RBSet!*)
module MemoTableInst = Subtree_inst.MemoTableInst (struct
  (*! structure IntSyn' = IntSyn !*)
  (*! structure CompSyn' = CompSyn !*)
  module Conv = Conv
  module Whnf = Whnf
  module Match = Match
  module Assign = Assign__
  module Print = Print

  (*! structure TableParam = TableParam !*)
  module AbstractTabled = AbstractTabled
  module Table = IntRedBlackTree
end)

(*! structure RBSet = RBSet!*)
module SwMemoTable = Sw_subtree.SwMemoTable (struct
  (*! structure TableParam = TableParam !*)
  module MemoTable = MemoTable
  module MemoTableInst = MemoTableInst
end)

module Tabled_ = Tabled_machine.Tabled (struct
  (*! structure IntSyn' = IntSyn !*)
  (*! structure CompSyn' = CompSyn !*)
  module Unify = UnifyTrail
  module Match = Match
  module TabledSyn = TabledSyn
  module Assign = Assign__
  module Index = Index
  module Queue = Queue.Queue

  (*! structure TableParam = TableParam !*)
  (*	  structure MemoTable = MemoTable    *)
  module MemoTable = SwMemoTable
  module AbstractTabled = AbstractTabled
  module CPrint = CPrint
  module Print = Print
end)

(*	  structure Names = Names*)
(*! structure Cs_manager = Cs_manager !*)
(*	  structure Subordinate = Subordinate*)
module PtRecon = Ptrecon.PtRecon (struct
  (*! structure IntSyn' = IntSyn !*)
  (*! structure CompSyn' = CompSyn !*)
  module Unify = UnifyTrail

  (*! structure TableParam = TableParam !*)
  module MemoTable = SwMemoTable
  module Assign = Assign__
  module Index = Index
  module CPrint = CPrint
  module Names = Names
end)

(*! structure Cs_manager = Cs_manager !*)
module Trace = Trace.Trace (struct
  (*! structure IntSyn' = IntSyn !*)
  module Names = Names
  module Whnf = Whnf
  module Abstract = Abstract
  module Print = Print
end)

module AbsMachineSbt = Absmachine_sbt.AbsMachineSbt (struct
  module IntSyn' = IntSyn
  module CompSyn' = CompSyn
  module SubTree = SubTree
  module Unify = UnifyTrail
  module Assign = Assign__
  module Index = Index
  module CPrint = CPrint
  module Print = Print
  module Names = Names
  module Cs_manager = Cs_manager
end)

module TMachine = Tmachine.TMachine (struct
  (*! structure IntSyn' = IntSyn !*)
  (*! structure CompSyn' = CompSyn !*)
  module Unify = UnifyTrail
  module Index = Index
  module Assign = Assign__
  module CPrint = CPrint
  module Names = Names
  module Trace = Trace
end)

(*! structure Cs_manager = Cs_manager !*)
module SwMachine = Swmachine.SwMachine (struct
  module Trace = Trace
  module AbsMachine = AbsMachine
  module TMachine = TMachine
end)
