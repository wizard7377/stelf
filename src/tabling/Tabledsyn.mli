include module type of Tabledsyn_intf

module MakeTabledSyn
    (Names : NAMES)
    (Table : TABLE with type key = int)
    (Index : INDEX) : TABLEDSYN
(*
  (*! structure IntSyn' : INTSYN !*)
  module Names : NAMES
  (*! sharing Names.IntSyn = IntSyn' !*)
  module Table : TABLE with type key = int
  module Index : INDEX
*)
