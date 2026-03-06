open! Basis;;
module ModSyn = (ModSyn)(struct
                           module Global = Global;;
                           (*! structure IntSyn' = IntSyn !*);;
                           module Names' = Names;;
                           (*! structure Paths' = Paths !*);;
                           module Origins = Origins;;
                           module Whnf = Whnf;;
                           module Strict = Strict;;
                           module IntTree = IntRedBlackTree;;
                           module HashTable = StringHashTable;;
                           end);;