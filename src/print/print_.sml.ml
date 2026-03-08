open! Basis
module SymbolAscii = Symbol.MakeSymbolAscii (struct end)
module SymbolTeX = Symbol.MakeSymbolTeX (struct end)

(*
structure WorldPrint = WorldPrint 
  (structure Global = Global
   ! structure IntSyn = IntSyn !
   ! structure Tomega' = Tomega !
   structure WorldSyn' = WorldSyn
   structure Names = Names
   structure Formatter_param = Formatter
   structure Print = Print);
*)
module Print = MakePrint (struct
  (*! structure IntSyn' = IntSyn !*)
  module Whnf = Whnf
  module Abstract = Abstract
  module Constraints = Constraints
  module Names = Names
  module Formatter_param = Formatter
  module Symbol = SymbolAscii
end)

module ClausePrint = Clause_print.MakeClausePrint (struct
  (*! structure IntSyn' = IntSyn !*)
  module Whnf = Whnf
  module Names = Names
  module Formatter_param = Formatter
  module Print = Print
  module Symbol = SymbolAscii
end)

module PrintTeX = MakePrint (struct
  (*! structure IntSyn' = IntSyn !*)
  module Whnf = Whnf
  module Abstract = Abstract
  module Constraints = Constraints
  module Names = Names
  module Formatter_param = Formatter
  module Symbol = SymbolTeX
end)

module ClausePrintTeX = Clause_print.MakeClausePrint (struct
  (*! structure IntSyn' = IntSyn !*)
  module Whnf = Whnf
  module Constraints = Constraints
  module Names = Names
  module Formatter_param = Formatter
  module Print = PrintTeX
  module Symbol = SymbolTeX
end)

module PrintTwega = Print_twega.MakePrintTwega (struct
  (*! structure IntSyn' = IntSyn !*)
  module Whnf = Whnf
  module Abstract = Abstract
  module Constraints = Constraints
  module Names = Names
  module Formatter_param = Formatter
end)

module PrintXML = Print_xml.MakePrintXML (struct
  (*! structure IntSyn' = IntSyn !*)
  module Whnf = Whnf
  module Abstract = Abstract
  module Constraints = Constraints
  module Names = Names
  module Formatter_param = Formatter
end)

module PrintOMDoc = Print_omdoc.MakePrintOMDoc (struct
  (*! structure IntSyn' = IntSyn !*)
  module Whnf = Whnf
  module Abstract = Abstract
  module Constraints = Constraints
  module Names = Names
  module Formatter_param = Formatter
end)
