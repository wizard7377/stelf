open Whnf_intf
include module type of Conv_intf

module Conv (Conv__0 : sig
  module Whnf : WHNF
end) : CONV
