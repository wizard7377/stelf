open! Basis
module Whnf__ = Whnf ()

module Conv__ = Conv (struct
  module Whnf = Whnf__
end)

module Tomega : TOMEGA = MakeTomega (struct
  module Whnf = Whnf__
  module Conv = Conv__
end)

include Tomega
