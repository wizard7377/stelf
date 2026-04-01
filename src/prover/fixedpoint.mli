include module type of Fixedpoint_intf

module FixedPoint (FixedPoint__0 : sig
  module State' : State.STATE
end) : FIXEDPOINT with module State = FixedPoint__0.State'
