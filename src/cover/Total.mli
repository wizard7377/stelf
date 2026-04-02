include module type of Total_intf

module Total (Total__0 : sig
  module Global : GLOBAL
  module Table : TABLE with type key = int

  (*! structure IntSyn' : INTSYN !*)
  module Whnf : WHNF

  (*! sharing Whnf.IntSyn = IntSyn' !*)
  module Names : NAMES

  (*! sharing Names.IntSyn = IntSyn' !*)
  module ModeTable : Modetable.MODETABLE

  (*! sharing ModeSyn.IntSyn = IntSyn' !*)
  module ModeCheck : Modecheck.MODECHECK
  module Index : INDEX

  (*! sharing Index.IntSyn = IntSyn' !*)
  module Subordinate : Subordinate.Subordinate_.SUBORDINATE

  (*! sharing Subordinate.IntSyn = IntSyn' !*)
  module Order : ORDER

  (*! sharing Order.IntSyn = IntSyn' !*)
  module Reduces : Reduces_intf.REDUCES

  (*! sharing Reduces.IntSyn = IntSyn' !*)
  module Cover : COVER

  (*! structure Paths : PATHS !*)
  module Origins : Origins.ORIGINS

  (*! sharing Origins.Paths = Paths !*)
  (*! sharing Origins.IntSyn = IntSyn' !*)
  module Timers : Timers.TIMERS
end) : TOTAL
