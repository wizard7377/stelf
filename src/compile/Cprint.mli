include module type of Cprint_intf

module Make_CPrint (CPrint__0 : sig
  (*! structure IntSyn' : INTSYN !*)
  (*! structure CompSyn' : COMPSYN !*)
  (*! sharing CompSyn'.IntSyn = IntSyn' !*)
  module Print : PRINT

  (*! sharing Print.IntSyn = IntSyn' !*)
  module Formatter : FORMATTER
  module Names : NAMES
end) : CPRINT
