open! Basis

module StyleCheck = MakeStyleCheck (struct
  module Whnf = Whnf
  module Index = Index
  module Origins = Origins
end)
