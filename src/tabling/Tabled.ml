(* # 1 "src/tabling/Tabled.sig.ml" *)

(* # 1 "src/tabling/Tabled.fun.ml" *)

(* # 1 "src/tabling/Tabled.sml.ml" *)
open! Basis

module TabledSyn = Tabledsyn.MakeTabledSyn (struct
  (*! structure IntSyn' = IntSyn !*)
  module Names = Names
  module Table = TableInstances.IntRedBlackTree
  module Index = Index
end)
