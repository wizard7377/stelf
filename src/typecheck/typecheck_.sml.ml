open! Basis;;
module TypeCheck = (TypeCheck)(struct
                                 (*! structure IntSyn' = IntSyn !*);;
                                 module Conv = Conv;;
                                 module Whnf = Whnf;;
                                 module Names = Names;;
                                 module Print = Print;;
                                 end);;
module Strict = (Strict)(struct
                           (*! structure IntSyn' = IntSyn !*);;
                           module Whnf = Whnf;;
                           module Paths' = Paths;;
                           end);;