open! Basis;;
module TabledSyn = (TabledSyn)(struct
                                 (*! structure IntSyn' = IntSyn !*);;
                                 module Names = Names;;
                                 module Table = IntRedBlackTree;;
                                 module Index = Index;;
                                 end);;