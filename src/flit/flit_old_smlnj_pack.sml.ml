open! Basis
(* Commented out: PACK_WORD not available
open! Basis;;
(* cope with nonstandard old smlnj name of PackWord32Little -jcreed 2006.9.15 *);;
module Flit = (Flit)(struct
                       module Global = Global;;
                       module Word = Word32;;
                       module Pack = Pack32Little;;
                       module IntSyn = IntSyn;;
                       module Whnf = Whnf;;
                       module Print = Print;;
                       module Names = Names;;
                       module Index = Index;;
                       module Table = IntRedBlackTree;;
                       end);;
*)
