open! Basis

(* Now in compsyn.fun *)
(*
structure CompSyn =
  CompSyn (structure Global = Global
           ! structure IntSyn' = IntSyn !
	   structure Names = Names
           structure Table = IntRedBlackTree);
*)
module CPrint = Cprint.Make_CPrint (struct
  (*! structure IntSyn' = IntSyn !*)
  (*! structure CompSyn' = CompSyn !*)
  module Print = Print
  module Formatter = Formatter
  module Names = Names
end)

module SubTree = Subtree.SubTree (struct
  module IntSyn' = IntSyn
  module Whnf = Whnf
  module Unify = UnifyTrail
  module CompSyn' = CompSyn
  module Print = Print
  module CPrint = CPrint
  module Names = Names
  module Formatter = Formatter
  module Cs_manager = Cs_manager
  module Table = IntRedBlackTree
  module RBSet = RBSet
end)

module Compile = MakeCompile (struct
  (*! structure IntSyn' = IntSyn !*)
  (*! structure CompSyn' = CompSyn !*)
  module Whnf = Whnf
  module TypeCheck = TypeCheck
  module SubTree = SubTree
  module CPrint = CPrint
  module Print = Print
  module Names = Names
end)

module Assign__ = Assign.Assign (struct
  (*! structure IntSyn' = IntSyn !*)
  module Whnf = Whnf
  module Unify = UnifyTrail
  module Print = Print
end)

(* Re-export module types that would otherwise be shadowed in downstream libraries *)
module type SUBTREE = Subtree.SUBTREE
module type CPRINT = Cprint.CPRINT
