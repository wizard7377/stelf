open Whnf_intf
include module type of Approx_intf

module MakeApprox (Approx__0 : sig
  module Whnf : WHNF
end) : APPROX
