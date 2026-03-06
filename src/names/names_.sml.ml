open! Basis;;
module Names = (Names)(struct
                         module Global = Global;;
                         (*! structure IntSyn' = IntSyn !*);;
                         module Constraints = Constraints;;
                         module HashTable = StringHashTable;;
                         module StringTree = StringRedBlackTree;;
                         end);;