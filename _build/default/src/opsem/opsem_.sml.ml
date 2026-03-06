open! Basis;;
module AbsMachine = (AbsMachine)(struct
                                   (*! structure IntSyn' = IntSyn !*);;
                                   (*! structure CompSyn' = CompSyn !*);;
                                   module Unify = UnifyTrail;;
                                   module Assign = Assign;;
                                   module Index = Index;;
                                   module CPrint = CPrint;;
                                   module Print = Print;;
                                   module Names = Names;;
                                   end);;
(*! structure CSManager = CSManager !*);;
module AbstractTabled = (AbstractTabled)(struct
                                           (*! structure IntSyn' = IntSyn !*);;
                                           module Print = Print;;
                                           module Whnf = Whnf;;
                                           module Unify = UnifyTrail;;
                                           module Constraints = Constraints;;
                                           module Subordinate = Subordinate;;
                                           (*! structure TableParam = TableParam !*);;
                                           module Conv = Conv;;
                                           module Print = Print;;
                                           end);;
module MemoTable = (MemoTable)(struct
                                 (*! structure IntSyn' = IntSyn !*);;
                                 (*! structure CompSyn' = CompSyn !*);;
                                 module Conv = Conv;;
                                 module Whnf = Whnf;;
                                 module Print = Print;;
                                 (*! structure TableParam = TableParam !*);;
                                 module AbstractTabled = AbstractTabled;;
                                 module Table = IntRedBlackTree;;
                                 end);;
(*! structure RBSet = RBSet!*);;
module MemoTableInst = (MemoTableInst)(struct
                                         (*! structure IntSyn' = IntSyn !*);;
                                         (*! structure CompSyn' = CompSyn !*);;
                                         module Conv = Conv;;
                                         module Whnf = Whnf;;
                                         module Match = Match;;
                                         module Assign = Assign;;
                                         module Print = Print;;
                                         (*! structure TableParam = TableParam !*);;
                                         module AbstractTabled = AbstractTabled;;
                                         module Table = IntRedBlackTree;;
                                         end);;
(*! structure RBSet = RBSet!*);;
module SwMemoTable = (SwMemoTable)(struct
                                     (*! structure TableParam = TableParam !*);;
                                     module MemoTable = MemoTable;;
                                     module MemoTableInst = MemoTableInst;;
                                     end);;
module Tabled = (Tabled)(struct
                           (*! structure IntSyn' = IntSyn !*);;
                           (*! structure CompSyn' = CompSyn !*);;
                           module Unify = UnifyTrail;;
                           module Match = Match;;
                           module TabledSyn = TabledSyn;;
                           module Assign = Assign;;
                           module Index = Index;;
                           module Queue = Queue;;
                           (*! structure TableParam = TableParam !*);;
                           (*	  structure MemoTable = MemoTable    *);;
                           module MemoTable = SwMemoTable;;
                           module AbstractTabled = AbstractTabled;;
                           module CPrint = CPrint;;
                           module Print = Print;;
                           end);;
(*	  structure Names = Names*);;
(*! structure CSManager = CSManager !*);;
(*	  structure Subordinate = Subordinate*);;
module PtRecon = (PtRecon)(struct
                             (*! structure IntSyn' = IntSyn !*);;
                             (*! structure CompSyn' = CompSyn !*);;
                             module Unify = UnifyTrail;;
                             (*! structure TableParam = TableParam !*);;
                             module MemoTable = SwMemoTable;;
                             module Assign = Assign;;
                             module Index = Index;;
                             module CPrint = CPrint;;
                             module Names = Names;;
                             end);;
(*! structure CSManager = CSManager !*);;
module Trace = (Trace)(struct
                         (*! structure IntSyn' = IntSyn !*);;
                         module Names = Names;;
                         module Whnf = Whnf;;
                         module Abstract = Abstract;;
                         module Print = Print;;
                         end);;
module AbsMachineSbt = (AbsMachineSbt)(struct
                                         module IntSyn' = IntSyn;;
                                         module CompSyn' = CompSyn;;
                                         module SubTree = SubTree;;
                                         module Unify = UnifyTrail;;
                                         module Assign = Assign;;
                                         module Index = Index;;
                                         module CPrint = CPrint;;
                                         module Print = Print;;
                                         module Names = Names;;
                                         module CSManager = CSManager;;
                                         end);;
module TMachine = (TMachine)(struct
                               (*! structure IntSyn' = IntSyn !*);;
                               (*! structure CompSyn' = CompSyn !*);;
                               module Unify = UnifyTrail;;
                               module Index = Index;;
                               module Assign = Assign;;
                               module CPrint = CPrint;;
                               module Names = Names;;
                               module Trace = Trace;;
                               end);;
(*! structure CSManager = CSManager !*);;
module SwMachine = (SwMachine)(struct
                                 module Trace = Trace;;
                                 module AbsMachine = AbsMachine;;
                                 module TMachine = TMachine;;
                                 end);;