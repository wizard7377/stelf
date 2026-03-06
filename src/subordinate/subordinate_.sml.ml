open! Basis;;
module MemoTable = (HashTable)(struct
                                 type nonrec key' = int * int;;
                                 let hash = function 
                                                     | (n, m) -> (7 * n) + m;;
                                 let eq (x__op, y__op) = x__op = y__op;;
                                 end);;
module Subordinate = (Subordinate)(struct
                                     module Global = Global;;
                                     (*! structure IntSyn' = IntSyn !*);;
                                     module Whnf = Whnf;;
                                     module Names = Names;;
                                     module Table = IntRedBlackTree;;
                                     module MemoTable = MemoTable;;
                                     module IntSet = IntSet;;
                                     end);;