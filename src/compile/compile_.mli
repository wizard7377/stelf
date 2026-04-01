include module type of Compile_intf

module MakeCompile (Compile__0 : sig
  (*! structure IntSyn' : INTSYN !*)
  (*! structure CompSyn' : COMPSYN !*)
  (*! sharing CompSyn'.IntSyn = IntSyn' !*)
  module Whnf : WHNF

  (*! sharing Whnf.IntSyn = IntSyn' !*)
  module TypeCheck : TYPECHECK

  (* sharing TypeCheck.IntSyn = IntSyn' !*)
  module SubTree : Subtree.SUBTREE

  (*! sharing SubTree.IntSyn = IntSyn' !*)
  (*! sharing SubTree.CompSyn = CompSyn' !*)
  (* CPrint currently unused *)
  module CPrint : Cprint.CPRINT

  (*! sharing CPrint.IntSyn = IntSyn' !*)
  (*! sharing CPrint.CompSyn = CompSyn' !*)
  (* CPrint currently unused *)
  module Print : PRINT

  (*! sharing Print.IntSyn = IntSyn' !*)
  module Names : NAMES
end) : COMPILE

module CPrint : Cprint.CPRINT
module SubTree : Subtree.SUBTREE
module Compile : COMPILE

module Assign__ : Assign.ASSIGN
