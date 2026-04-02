open Integers
include module type of Rationals_intf

module Rationals (Integers : INTEGERS) :
  RATIONALS with type Integers.int = Integers.int
