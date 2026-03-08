open! Basis

module Names = MakeNames (struct
  module Global = Global

  (*! structure IntSyn' = IntSyn !*)
  module Constraints = Constraints
  module HashTable = Table_instances.StringHashTable
  module StringTree = Table_instances.StringRedBlackTree
end)
