(* # 1 "src/domains/Domains_.sig.ml" *)

(* # 1 "src/domains/Domains_.fun.ml" *)

(* # 1 "src/domains/Domains_.sml.ml" *)
open IntegersMod

module Integers_ : Integers.INTEGERS
module Rationals_ : Rationals.RATIONALS with type Integers.int = Integers_.int
module IntegersMod7 : Field.FIELD
