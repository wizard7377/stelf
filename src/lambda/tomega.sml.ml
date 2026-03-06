open! Basis;;
module Whnf = (Whnf)(struct
                       
                       end);;
(*! structure IntSyn' = IntSyn !*);;
module Conv = (Conv)(struct
                       (*! structure IntSyn' = IntSyn !*);;
                       module Whnf = Whnf;;
                       end);;
module Tomega : TOMEGA =
  (Tomega)(struct
             (*! structure IntSyn' = IntSyn !*);;
             module Whnf = Whnf;;
             module Conv = Conv;;
             end);;