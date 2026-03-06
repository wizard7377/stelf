# 1 "src/flit/flit_old_smlnj_pack.sig.ml"

# 1 "src/flit/flit_old_smlnj_pack.fun.ml"

# 1 "src/flit/flit_old_smlnj_pack.sml.ml"
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