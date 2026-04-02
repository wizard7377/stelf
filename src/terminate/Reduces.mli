include module type of Reduces_intf

module Reduces (Reduces__0 : sig
  module Global : GLOBAL

  (*! structure IntSyn' : INTSYN !*)
  module Whnf : WHNF

  (*! sharing Whnf.IntSyn = IntSyn' !*)
  module Names : NAMES

  (*! sharing Names.IntSyn = IntSyn' !*)
  module Index : INDEX

  (*! sharing Index.IntSyn = IntSyn' !*)
  module Subordinate : Subordinate.Subordinate_.SUBORDINATE

  (*! sharing Subordinate.IntSyn = IntSyn' !*)
  module Formatter : FORMATTER
  module Print : PRINT

  (*! sharing Print.IntSyn = IntSyn' !*)
  module Order : ORDER

  (*! sharing Order.IntSyn = IntSyn' !*)
  (*! structure Paths  : PATHS !*)
  module Checking : Checking.CHECKING

  (*! sharing Checking.IntSyn = IntSyn' !*)
  (*! sharing Checking.Paths = Paths !*)
  module Origins : Origins.ORIGINS
end) : REDUCES
