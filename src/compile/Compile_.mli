include module type of Compile_intf

module MakeCompile
    (Whnf : WHNF)
    (TypeCheck : TYPECHECK)
    (SubTree : Subtree.SUBTREE)
    (CPrint : Cprint.CPRINT)
    (Print : PRINT)
    (Names : NAMES) :
  COMPILE
(*
  (*! structure IntSyn' : INTSYN !*)
  (*! structure CompSyn' : COMPSYN !*)
  (*! sharing CompSyn'.IntSyn = IntSyn' !*)
  (*! sharing Whnf.IntSyn = IntSyn' !*)
  (* sharing TypeCheck.IntSyn = IntSyn' !*)
  (*! sharing SubTree.IntSyn = IntSyn' !*)
  (*! sharing SubTree.CompSyn = CompSyn' !*)
  (*! sharing CPrint.IntSyn = IntSyn' !*)
  (*! sharing CPrint.CompSyn = CompSyn' !*)
  (*! sharing Print.IntSyn = IntSyn' !*)
*)

module CPrint : Cprint.CPRINT
module SubTree : Subtree.SUBTREE
module Compile : COMPILE

module Assign__ : Assign.ASSIGN
