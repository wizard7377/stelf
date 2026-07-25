include module type of FIXEDPOINT

module FixedPoint (FixedPoint__0 : sig
  module State' : State.STATE
end) : FIXEDPOINT with module State = FixedPoint__0.State'
