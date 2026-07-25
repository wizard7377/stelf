include module type of NAMES

module MakeNames
    (Global : GLOBAL)
    (Constraints : CONSTRAINTS)
    (HashTable : TABLE with type key = string)
    (StringTree : TABLE with type key = string) : NAMES
(*
  (*! structure IntSyn' : INTSYN !*)
  (*! sharing Constraints.IntSyn = IntSyn' !*)
*)

module Names : NAMES
include NAMES
