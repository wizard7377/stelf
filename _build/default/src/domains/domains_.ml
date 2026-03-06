# 1 "src/domains/domains_.sig.ml"

# 1 "src/domains/domains_.fun.ml"

# 1 "src/domains/domains_.sml.ml"
open! Basis;;
module Integers = (Integers)(struct
                               ;;intInf_;;
                               end);;
module Rationals = (Rationals)(struct
                                 ;;integers_;;
                                 end);;
module IntegersMod7 = (IntegersMod)(struct
                                      let p = 7;;
                                      end);;