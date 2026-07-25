module Make_Resugar
    (Syntax : Syntax.SYNTAX)
    (Cst : Cst.CST)
(* : RESUGAR.RESUGAR with module Syntax = Syntax with module Cst = Cst *) =
struct
  module Syntax = Syntax
  module Cst = Cst

  let register = assert false
  let resugar = assert false
end
