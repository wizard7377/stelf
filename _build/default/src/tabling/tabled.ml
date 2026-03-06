# 1 "src/tabling/tabled.sig.ml"

# 1 "src/tabling/tabled.fun.ml"

# 1 "src/tabling/tabled.sml.ml"
open! Basis;;
module TabledSyn = (TabledSyn)(struct
                                 (*! structure IntSyn' = IntSyn !*);;
                                 module Names = Names;;
                                 module Table = IntRedBlackTree;;
                                 module Index = Index;;
                                 end);;