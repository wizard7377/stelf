include module type of Names_intf

module MakeNames (Names__0 : sig
  module Global : GLOBAL

  (*! structure IntSyn' : INTSYN !*)
  module Constraints : CONSTRAINTS

  (*! sharing Constraints.IntSyn = IntSyn' !*)
  module HashTable : TABLE with type key = string
  module StringTree : TABLE with type key = string
end) : NAMES

module Names : NAMES
include NAMES
