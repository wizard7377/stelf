include module type of Tabledsyn_intf

module MakeTabledSyn (TabledSyn__0 : sig
  (*! structure IntSyn' : INTSYN !*)
  module Names : NAMES

  (*! sharing Names.IntSyn = IntSyn' !*)
  module Table : TABLE with type key = int
  module Index : INDEX
end) : TABLEDSYN
