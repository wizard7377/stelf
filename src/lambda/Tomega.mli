include module type of Tomega_intf

module MakeTomega (Tomega__0 : sig
  module Whnf : Whnf.WHNF
  module Conv : Conv.CONV
end) : TOMEGA

module Tomega : TOMEGA

