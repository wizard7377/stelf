open! Basis;;
(* Now in compsyn.fun *);;
(*
structure CompSyn =
  CompSyn (structure Global = Global
           ! structure IntSyn' = IntSyn !
	   structure Names = Names
           structure Table = IntRedBlackTree);
*);;
module CPrint = (CPrint)(struct
                           (*! structure IntSyn' = IntSyn !*);;
                           (*! structure CompSyn' = CompSyn !*);;
                           module Print = Print;;
                           module Formatter = Formatter;;
                           module Names = Names;;
                           end);;
module SubTree = (SubTree)(struct
                             module IntSyn' = IntSyn;;
                             module Whnf = Whnf;;
                             module Unify = UnifyTrail;;
                             module CompSyn' = CompSyn;;
                             module Print = Print;;
                             module CPrint = CPrint;;
                             module Names = Names;;
                             module Formatter = Formatter;;
                             module CSManager = CSManager;;
                             module Table = IntRedBlackTree;;
                             module RBSet = RBSet;;
                             end);;
module Compile = (Compile)(struct
                             (*! structure IntSyn' = IntSyn !*);;
                             (*! structure CompSyn' = CompSyn !*);;
                             module Whnf = Whnf;;
                             module TypeCheck = TypeCheck;;
                             module SubTree = SubTree;;
                             module CPrint = CPrint;;
                             module Print = Print;;
                             module Names = Names;;
                             end);;
module Assign = (Assign)(struct
                           (*! structure IntSyn' = IntSyn !*);;
                           module Whnf = Whnf;;
                           module Unify = UnifyTrail;;
                           module Print = Print;;
                           end);;