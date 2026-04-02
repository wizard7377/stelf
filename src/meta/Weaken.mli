include module type of Weaken_intf

module Make_Weaken (Weaken__0 : sig
  module Whnf : WHNF
end) : Weaken_intf.WEAKEN
