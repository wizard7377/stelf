open! Basis

module UniqueTable = ModeTable (struct
  module Table = IntRedBlackTree
end)

module UniqueCheck = ModeCheck (struct
  module ModeTable = UniqueTable
  module Whnf = Whnf
  module Index = Index
  module Origins = Origins
end)

module Unique = Unique (struct
  module Global = Global
  module Whnf = Whnf
  module Abstract = Abstract
  module Unify = UnifyTrail
  module Constraints = Constraints
  module UniqueTable = UniqueTable
  module UniqueCheck = UniqueCheck
  module Index = Index
  module Subordinate = Subordinate
  module WorldSyn = WorldSyn
  module Names = Names
  module Print = Print
  module TypeCheck = TypeCheck
  module Timers = Timers
end)
