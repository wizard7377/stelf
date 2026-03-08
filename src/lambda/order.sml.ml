open! Basis
open Table_instances

module Order = MakeOrder (struct
  (*! structure IntSyn' = IntSyn !*) module Table = IntRedBlackTree
end)

include Order
(* -bp *)
(*
structure RedOrder = 
    RedOrder (! structure IntSyn' = IntSyn !
	      structure Table = IntRedBlackTree); 
*)
