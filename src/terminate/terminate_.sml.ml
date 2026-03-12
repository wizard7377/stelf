open! Basis
open Checking
open Reduces

module type CHECKING = CHECKING
module type REDUCES = REDUCES

module Checking = Checking (struct
  module Global = Global

  (*! structure IntSyn' = IntSyn !*)
  module Whnf = Whnf
  module Conv = Conv
  module Unify = UnifyTrail
  module Trail = Trail
  module Names = Names
  module Index = Index
  module Subordinate = Subordinate
  module Formatter = Formatter
  module Print = Print
  module Order = Order
  module Paths = Paths
  module Origins = Origins
end)

(*! structure Cs_manager = Cs_manager !*)
module Reduces = Reduces (struct
  module Global = Global

  (*! structure IntSyn' = IntSyn !*)
  module Whnf = Whnf
  module Names = Names
  module Index = Index
  module Subordinate = Subordinate
  module Formatter = Formatter
  module Print = Print
  module Order = Order
  module Checking = Checking
  module Paths = Paths
  module Origins = Origins
end)
(*! structure Cs_manager = Cs_manager !*)
