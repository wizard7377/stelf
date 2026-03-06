open! Basis;;
(* structure ModeSyn  in modesyn.sml *);;
module ModeTable = (ModeTable)(struct
                                 module Table = IntRedBlackTree;;
                                 end);;
module ModeDec = (ModeDec)(struct
                             
                             end);;
(*! structure ModeSyn' = ModeSyn !*);;
(*! structure Paths' = Paths !*);;
module ModeCheck = (ModeCheck)(struct
                                 (*! structure IntSyn = IntSyn !*);;
                                 module ModeTable = ModeTable;;
                                 module Whnf = Whnf;;
                                 module Index = Index;;
                                 (*! structure Paths = Paths !*);;
                                 module Origins = Origins;;
                                 end);;
module ModePrint = (ModePrint)(struct
                                 (*! structure ModeSyn' = ModeSyn !*);;
                                 module Names = Names;;
                                 module Formatter = Formatter;;
                                 module Print = Print;;
                                 end);;