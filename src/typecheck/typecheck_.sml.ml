open! Basis

module type STRICT = Strict.STRICT

module TypeCheck = MakeTypeCheck (struct
  (*! structure IntSyn' = IntSyn !*)
  module Conv = Conv
  module Whnf = Whnf
  module Names = Names
  module Print = Print
end)

module Strict = Strict.Strict (struct
  (*! structure IntSyn' = IntSyn !*) module Whnf = Whnf
end)
