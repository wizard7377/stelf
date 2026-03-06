open! Basis;;
module Flit = (Flit)(struct
                       module Global = Global;;
                       module Word = Word32;;
                       module Pack = PackWord32Little;;
                       module IntSyn = IntSyn;;
                       module Whnf = Whnf;;
                       module Print = Print;;
                       module Names = Names;;
                       module Index = Index;;
                       module Table = IntRedBlackTree;;
                       end);;