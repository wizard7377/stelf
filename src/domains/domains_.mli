(* # 1 "src/domains/domains_.sig.ml" *)

(* # 1 "src/domains/domains_.fun.ml" *)

(* # 1 "src/domains/domains_.sml.ml" *)
open Integers_mod

module Integers_ : Integers.INTEGERS
module Rationals_ : Rationals.RATIONALS with type Integers.int = Integers_.int
module IntegersMod7 : Field.FIELD
