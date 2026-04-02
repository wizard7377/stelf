(* # 1 "src/terminate/Terminate_.sig.ml" *)

(* # 1 "src/terminate/Terminate_.fun.ml" *)

(* # 1 "src/terminate/Terminate_.sml.ml" *)
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
  module Subordinate = Subordinate.Subordinate_.Subordinate
  module Formatter = Formatter__Formatter_.Formatter
  module Print = Print
  module Order = Order
  module Paths = Paths
  module Origins = Origins
end)

(*! structure CsManager = CsManager !*)
module Reduces = Reduces (struct
  module Global = Global

  (*! structure IntSyn' = IntSyn !*)
  module Whnf = Whnf
  module Names = Names
  module Index = Index
  module Subordinate = Subordinate.Subordinate_.Subordinate
  module Formatter = Formatter__Formatter_.Formatter
  module Print = Print
  module Order = Order
  module Checking = Checking
  module Paths = Paths
  module Origins = Origins
end)
(*! structure CsManager = CsManager !*)
