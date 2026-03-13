(* # 1 "src/tabling/tabled.sig.ml" *)

(* # 1 "src/tabling/tabled.fun.ml" *)

(* # 1 "src/tabling/tabled.sml.ml" *)
open! Basis

module TabledSyn = Tabledsyn.MakeTabledSyn (struct
  (*! structure IntSyn' = IntSyn !*)
  module Names = Names
  module Table = Table_instances.IntRedBlackTree
  module Index = Index
end)
