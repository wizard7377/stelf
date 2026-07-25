(* # 1 "src/opsem/Opsem_.sig.ml" *)

(* # 1 "src/opsem/Opsem_.fun.ml" *)

(* # 1 "src/opsem/Opsem_.sml.ml" *)
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

(*! structure CsManager = CsManager !*)
module AbstractTabled_ = AbstractTabled.AbstractTabled (struct
  (*! structure IntSyn' = IntSyn !*)
  module Print = Print
  module Whnf = Whnf
  module Unify = UnifyTrail
  module Constraints = Constraints
  module Subordinate = Subordinate.Subordinate_.Subordinate

  (*! structure TableParam = TableParam !*)
  module Conv = Conv
end)

module MemoTable_ = MemoTable.MemoTable (struct
  (*! structure IntSyn' = IntSyn !*)
  (*! structure CompSyn' = CompSyn !*)
  module Conv = Conv
  module Whnf = Whnf
  module Print = Print

  (*! structure TableParam = TableParam !*)
  module AbstractTabled = AbstractTabled_
  module Table = TableInstances.IntRedBlackTree
end)

(*! structure RBSet = RBSet!*)
module MemoTableInst_ = SubtreeInst.MemoTableInst (struct
  (*! structure IntSyn' = IntSyn !*)
  (*! structure CompSyn' = CompSyn !*)
  module Conv = Conv
  module Whnf = Whnf
  module Match = Match
  module Assign = Assign__
  module Print = Print

  (*! structure TableParam = TableParam !*)
  module AbstractTabled = AbstractTabled_
  module Table = TableInstances.IntRedBlackTree
end)

module SwMemoTable_ = SwSubtree.SwMemoTable (struct
  (*! structure TableParam = TableParam !*)
  module MemoTable = MemoTable_
  module MemoTableInst = MemoTableInst_
end)

module Tabled_ = TabledMachine.Tabled (struct
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
  module MemoTable = SwMemoTable_
  module AbstractTabled = AbstractTabled_
  module CPrint = CPrint
  module Print = Print
end)

(*	  structure Names = Names*)
(*! structure CsManager = CsManager !*)
(*	  structure Subordinate = Subordinate*)
module PtRecon = Ptrecon.PtRecon (struct
  (*! structure IntSyn' = IntSyn !*)
  (*! structure CompSyn' = CompSyn !*)
  module Unify = UnifyTrail

  (*! structure TableParam = TableParam !*)
  module MemoTable = SwMemoTable_
  module Assign = Assign__
  module Index = Index
  module CPrint = CPrint
  module Names = Names
end)

(*! structure CsManager = CsManager !*)
module Trace = Trace.Trace (struct
  (*! structure IntSyn' = IntSyn !*)
  module Names = Names
  module Whnf = Whnf
  module Abstract = Abstract
  module Print = Print
end)

module AbsMachineSbt = AbsmachineSbt.AbsMachineSbt (struct
  module IntSyn' = IntSyn
  module CompSyn' = CompSyn
  module SubTree = SubTree
  module Unify = UnifyTrail
  module Assign = Assign__
  module Index = Index
  module CPrint = CPrint
  module Print = Print
  module Names = Names
  module CsManager = CsManager
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

(*! structure CsManager = CsManager !*)
module SwMachine = Swmachine.SwMachine (struct
  module Trace = Trace
  module AbsMachine = AbsMachine
  module TMachine = TMachine
end)
