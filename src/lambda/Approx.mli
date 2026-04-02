open Whnf_intf
include module type of Approx_intf

module MakeApprox (Whnf : WHNF) : APPROX
