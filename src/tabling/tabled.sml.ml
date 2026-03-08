open! Basis

module TabledSyn = Tabledsyn.MakeTabledSyn (struct
  (*! structure IntSyn' = IntSyn !*)
  module Names = Names
  module Table = Table_instances.IntRedBlackTree
  module Index = Index
end)
