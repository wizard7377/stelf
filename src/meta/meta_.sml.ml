open! Basis

module MTPGlobal = MTPGlobal (struct
  module MetaGlobal = MetaGlobal
end)

(* Now in funsyn.fun *)
(*
structure FunSyn = 
  FunSyn (! structure IntSyn' = IntSyn !
	  structure Whnf = Whnf
	  structure Conv = Conv);
*)
module StateSyn = StateSyn (struct
  (*! structure FunSyn' = FunSyn !*)
  (*! structure IntSyn' = IntSyn !*)
  module Whnf = Whnf
  module Conv = Conv
end)

module FunNames = FunNames (struct
  module Global = Global

  (*! structure FunSyn' = FunSyn !*)
  module HashTable = Table_instances.StringHashTable
end)

module FunPrint = FunPrint (struct
  (*! structure FunSyn' = FunSyn !*)
  module Formatter = Formatter
  module Print = Print
  module Names = Names
end)

(* moves eventually into the Twelf core *)
module Weaken = Weaken (struct
  (*! structure IntSyn' = IntSyn !*) module Whnf = Whnf
end)

module FunWeaken = FunWeaken (struct
  (*! structure FunSyn' = FunSyn !*) module Weaken = Weaken
end)

module FunTypeCheck = FunTypeCheck (struct
  (*! structure FunSyn' = FunSyn !*)
  module StateSyn' = StateSyn
  module Abstract = Abstract
  module TypeCheck = TypeCheck
  module Conv = Conv
  module Weaken = Weaken
  module Subordinate = Subordinate
  module Whnf = Whnf
  module Print = Print
  module FunPrint = FunPrint
end)

module RelFun = RelFun (struct
  module Global = Global

  (*! structure FunSyn' = FunSyn !*)
  module ModeTable = ModeTable
  module Names = Names
  module TypeCheck = TypeCheck
  module Trail = Trail
  module Unify = UnifyTrail
  module Whnf = Whnf
  module Print = Print
  module Weaken = Weaken
  module FunWeaken = FunWeaken
  module FunNames = FunNames
end)

(* Functor instantiation for the Prover *)
module MTPData = MTPData (struct
  module MTPGlobal = MTPGlobal
end)

module MTPAbstract = MTPAbstract (struct
  (*! structure IntSyn' = IntSyn !*)
  (*! structure FunSyn' = FunSyn !*)
  module StateSyn' = StateSyn
  module Whnf = Whnf
  module Constraints = Constraints
  module Unify = UnifyTrail
  module Subordinate = Subordinate
  module TypeCheck = TypeCheck
  module FunTypeCheck = FunTypeCheck
  module Abstract = Abstract
end)

module MTPInit = MTPInit (struct
  module MTPGlobal = MTPGlobal

  (*! structure IntSyn = IntSyn !*)
  module Names = Names

  (*! structure FunSyn' = FunSyn !*)
  module StateSyn' = StateSyn
  module MTPData = MTPData
  module Formatter = Formatter
  module Whnf = Whnf
  module Print = Print
  module FunPrint = FunPrint
end)

module MTPrint = MTPrint (struct
  module Global = Global

  (*! structure IntSyn = IntSyn !*)
  (*! structure FunSyn = FunSyn !*)
  module Names = Names
  module StateSyn' = StateSyn
  module Formatter' = Formatter
  module Print = Print
  module FunPrint = FunPrint
end)

module MTPSearch = MTPSearch (struct
  module Global = Global
  module MTPGlobal = MTPGlobal

  (*! structure IntSyn' = IntSyn !*)
  module Abstract = Abstract
  module Conv = Conv
  module StateSyn' = StateSyn

  (*! structure CompSyn' = CompSyn !*)
  module Compile = Compile
  module Whnf = Whnf
  module Unify = UnifyTrail
  module Index = IndexSkolem
  module Assign = Assign
  module CPrint = CPrint
  module Print = Print
  module Names = Names
end)

(*! structure Cs_manager = Cs_manager  !*)
module MTPFilling = MTPFilling (struct
  module MTPGlobal = MTPGlobal

  (*! structure IntSyn = IntSyn !*)
  (*! structure FunSyn' = FunSyn !*)
  module StateSyn' = StateSyn
  module MTPData = MTPData
  module Whnf = Whnf
  module Abstract = Abstract
  module TypeCheck = TypeCheck
  module Search = MTPSearch
  module Whnf = Whnf
end)

module MTPSplitting = MTPSplitting (struct
  module MTPGlobal = MTPGlobal
  module Global = Global

  (*! structure IntSyn = IntSyn !*)
  (*! structure FunSyn = FunSyn !*)
  module StateSyn' = StateSyn
  module Heuristic = Heuristic
  module MTPrint = MTPrint
  module MTPAbstract = MTPAbstract
  module Names = Names

  (* to be removed -cs *)
  module Conv = Conv
  module Whnf = Whnf
  module TypeCheck = TypeCheck
  module Subordinate = Subordinate
  module FunTypeCheck = FunTypeCheck
  module Index = Index
  module Print = Print
  module Unify = UnifyTrail
end)

(*! structure Cs_manager = Cs_manager !*)
module UniqueSearch = UniqueSearch (struct
  module Global = Global

  (*! structure IntSyn' = IntSyn !*)
  (*! structure FunSyn' = FunSyn !*)
  module StateSyn' = StateSyn
  module Abstract = Abstract
  module MTPGlobal = MTPGlobal

  (*! structure CompSyn' = CompSyn !*)
  module Whnf = Whnf
  module Unify = UnifyTrail
  module Assign = Assign
  module Index = Index
  module Compile = Compile
  module CPrint = CPrint
  module Print = Print
  module Names = Names
end)

(*! structure Cs_manager = Cs_manager !*)
module Inference = Inference (struct
  module MTPGlobal = MTPGlobal

  (*! structure IntSyn = IntSyn !*)
  (*! structure FunSyn' = FunSyn !*)
  module StateSyn' = StateSyn
  module Abstract = Abstract
  module TypeCheck = TypeCheck
  module FunTypeCheck = FunTypeCheck
  module UniqueSearch = UniqueSearch
  module Whnf = Whnf
  module Print = Print
end)

module MTPRecursion = MTPRecursion (struct
  module MTPGlobal = MTPGlobal
  module Global = Global

  (*! structure IntSyn = IntSyn !*)
  (*! structure FunSyn = FunSyn !*)
  module StateSyn' = StateSyn
  module FunTypeCheck = FunTypeCheck
  module MTPSearch = MTPSearch
  module Abstract = Abstract
  module MTPAbstract = MTPAbstract
  module Whnf = Whnf
  module Unify = UnifyTrail
  module Conv = Conv
  module Names = Names
  module Subordinate = Subordinate
  module MTPrint = MTPrint
  module Print = Print
  module TypeCheck = TypeCheck
  module FunPrint = FunPrint
  module Formatter = Formatter
end)

(*! structure Cs_manager = Cs_manager !*)
module MTPStrategy = MTPStrategy (struct
  module MTPGlobal = MTPGlobal
  module StateSyn' = StateSyn
  module MTPrint = MTPrint
  module MTPData = MTPData
  module MTPFilling = MTPFilling
  module MTPSplitting = MTPSplitting
  module MTPRecursion = MTPRecursion
  module Inference = Inference
  module Timers = Timers
end)

module MTProver = MTProver (struct
  module MTPGlobal = MTPGlobal

  (*! structure IntSyn' = IntSyn !*)
  (*! structure FunSyn = FunSyn !*)
  module StateSyn = StateSyn
  module Order = Order
  module MTPrint = MTPrint
  module MTPInit = MTPInit
  module MTPStrategy = MTPStrategy
  module RelFun = RelFun
end)

module CombiProver = CombiProver (struct
  module MTPGlobal = MTPGlobal

  (*! structure IntSyn' = IntSyn !*)
  module ProverNew = MTProver
  module ProverOld = Prover
end)

module MTPi = MTPi (struct
  module MTPGlobal = MTPGlobal

  (*! structure IntSyn = IntSyn !*)
  (*! structure FunSyn' = FunSyn !*)
  module StateSyn' = StateSyn
  module FunTypeCheck = FunTypeCheck
  module RelFun = RelFun
  module Formatter = Formatter
  module Print = Print
  module MTPrint = MTPrint
  module MTPInit = MTPInit
  module MTPFilling = MTPFilling
  module MTPData = MTPData
  module MTPSplitting = MTPSplitting
  module MTPRecursion = MTPRecursion
  module Inference = Inference
  module MTPStrategy = MTPStrategy
  module Names = Names
  module Order = Order
  module Timers = Timers
  module Ring = Ring
end)
