include module type of Absmachine_intf

module AbsMachine (AbsMachine__0 : sig
  (*! structure IntSyn' : INTSYN !*)
  (*! structure CompSyn' : COMPSYN !*)
  (*! sharing CompSyn'.IntSyn = IntSyn' !*)
  module Unify : UNIFY

  (*! sharing Unify.IntSyn = IntSyn' !*)
  module Assign : ASSIGN

  (*! sharing Assign.IntSyn = IntSyn' !*)
  module Index : INDEX

  (*! sharing Index.IntSyn = IntSyn' !*)
  (* CPrint currently unused *)
  module CPrint : Cprint.CPRINT

  (*! sharing CPrint.IntSyn = IntSyn' !*)
  (*! sharing CPrint.CompSyn = CompSyn' !*)
  module Print : PRINT

  (*! sharing Print.IntSyn = IntSyn' !*)
  module Names : NAMES
end) : ABSMACHINE
