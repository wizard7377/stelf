open WHNF
include module type of CONV

module Conv (Conv__0 : sig
  module Whnf : WHNF
end) : CONV
