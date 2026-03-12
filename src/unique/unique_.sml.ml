open! Basis

module UniqueTable = Modetable.MakeModeTable (struct
  module Table = Table_instances.IntRedBlackTree
end)

module UniqueCheck = Modecheck.MakeModeCheck (struct
  module ModeTable = UniqueTable
  module Whnf = Whnf
  module Index = Index
  module Origins = Origins
end)

include Unique (struct
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
  module Timers = Timers.Timers
end)
