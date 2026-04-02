include module type of Funsyn_intf

module Make_FunSyn (Whnf : WHNF) (Conv : CONV) : FUNSYN

module FunSyn : FUNSYN
