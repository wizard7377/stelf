open! Basis;;
module ThmSyn = (ThmSyn)(struct
                           (*! structure IntSyn = IntSyn !*);;
                           (*! structure ModeSyn' = ModeSyn !*);;
                           module Abstract = Abstract;;
                           module Whnf = Whnf;;
                           module Paths' = Paths;;
                           module Names' = Names;;
                           end);;
module ThmPrint = (ThmPrint)(struct
                               module ThmSyn' = ThmSyn;;
                               module Formatter = Formatter;;
                               end);;
module Thm = (Thm)(struct
                     module Global = Global;;
                     module ThmSyn' = ThmSyn;;
                     module TabledSyn = TabledSyn;;
                     (*       structure RedOrder = RedOrder *);;
                     (* -bp *);;
                     module Order = Order;;
                     module ModeTable = ModeTable;;
                     module ThmPrint = ThmPrint;;
                     module Paths' = Paths;;
                     end);;