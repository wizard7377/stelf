open Integers
include module type of RATIONALS

module Rationals (Integers : INTEGERS) :
  RATIONALS with type Integers.int = Integers.int
