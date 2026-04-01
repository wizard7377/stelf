include module type of Subordinate_intf

module MakeSubordinate (Subordinate__0 : sig
  module Global : GLOBAL

  (*! structure IntSyn' : INTSYN !*)
  module Whnf : WHNF

  (*! sharing Whnf.IntSyn = IntSyn' !*)
  module Names : NAMES

  (*! sharing Names.IntSyn = IntSyn' !*)
  module Table : TABLE with type key = int
  module MemoTable : TABLE with type key = int * int
  module IntSet : Intset.INTSET
end) : SUBORDINATE

module Subordinate : SUBORDINATE
