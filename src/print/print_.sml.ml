open! Basis;;
module SymbolAscii = (SymbolAscii)(struct
                                     
                                     end);;
module SymbolTeX = (SymbolTeX)(struct
                                 
                                 end);;
(*
structure WorldPrint = WorldPrint 
  (structure Global = Global
   ! structure IntSyn = IntSyn !
   ! structure Tomega' = Tomega !
   structure WorldSyn' = WorldSyn
   structure Names = Names
   structure Formatter' = Formatter
   structure Print = Print);
*);;
module Print = (Print)(struct
                         (*! structure IntSyn' = IntSyn !*);;
                         module Whnf = Whnf;;
                         module Abstract = Abstract;;
                         module Constraints = Constraints;;
                         module Names = Names;;
                         module Formatter' = Formatter;;
                         module Symbol = SymbolAscii;;
                         end);;
module ClausePrint = (ClausePrint)(struct
                                     (*! structure IntSyn' = IntSyn !*);;
                                     module Whnf = Whnf;;
                                     module Names = Names;;
                                     module Formatter' = Formatter;;
                                     module Print = Print;;
                                     module Symbol = SymbolAscii;;
                                     end);;
module PrintTeX = (Print)(struct
                            (*! structure IntSyn' = IntSyn !*);;
                            module Whnf = Whnf;;
                            module Abstract = Abstract;;
                            module Constraints = Constraints;;
                            module Names = Names;;
                            module Formatter' = Formatter;;
                            module Symbol = SymbolTeX;;
                            end);;
module ClausePrintTeX = (ClausePrint)(struct
                                        (*! structure IntSyn' = IntSyn !*);;
                                        module Whnf = Whnf;;
                                        module Constraints = Constraints;;
                                        module Names = Names;;
                                        module Formatter' = Formatter;;
                                        module Print = PrintTeX;;
                                        module Symbol = SymbolTeX;;
                                        end);;
module PrintTwega = (PrintTwega)(struct
                                   (*! structure IntSyn' = IntSyn !*);;
                                   module Whnf = Whnf;;
                                   module Abstract = Abstract;;
                                   module Constraints = Constraints;;
                                   module Names = Names;;
                                   module Formatter' = Formatter;;
                                   end);;
module PrintXML = (PrintXML)(struct
                               (*! structure IntSyn' = IntSyn !*);;
                               module Whnf = Whnf;;
                               module Abstract = Abstract;;
                               module Constraints = Constraints;;
                               module Names = Names;;
                               module Formatter' = Formatter;;
                               end);;
module PrintOMDoc = (PrintOMDoc)(struct
                                   (*! structure IntSyn' = IntSyn !*);;
                                   module Whnf = Whnf;;
                                   module Abstract = Abstract;;
                                   module Constraints = Constraints;;
                                   module Names = Names;;
                                   module Formatter' = Formatter;;
                                   end);;