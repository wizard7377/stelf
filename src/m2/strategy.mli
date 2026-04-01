include module type of Strategy_intf

module StrategyFRS (StrategyFRS__0 : sig
  module MetaGlobal : Meta_global.METAGLOBAL
  module MetaSyn' : Metasyn.METASYN
  module Filling : Filling_intf.FILLING with module MetaSyn = MetaSyn'
  module Splitting : Splitting_intf.SPLITTING with module MetaSyn = MetaSyn'
  module Recursion : Recursion_intf.RECURSION with module MetaSyn = MetaSyn'
  module Lemma : Lemma_intf.LEMMA with module MetaSyn = MetaSyn'
  module Qed : Qed_intf.QED with module MetaSyn = MetaSyn'
  module MetaPrint : Meta_print.METAPRINT with module MetaSyn = MetaSyn'
  module Timers : Timers_intf.TIMERS
end) : Strategy_intf.STRATEGY with module MetaSyn = StrategyFRS__0.MetaSyn'

module StrategyRFS (StrategyRFS__1 : sig
  module MetaGlobal : Meta_global.METAGLOBAL
  module MetaSyn' : Metasyn.METASYN
  module Filling : Filling_intf.FILLING with module MetaSyn = MetaSyn'
  module Splitting : Splitting_intf.SPLITTING with module MetaSyn = MetaSyn'
  module Recursion : Recursion_intf.RECURSION with module MetaSyn = MetaSyn'
  module Lemma : Lemma_intf.LEMMA with module MetaSyn = MetaSyn'
  module Qed : Qed_intf.QED with module MetaSyn = MetaSyn'
  module MetaPrint : Meta_print.METAPRINT with module MetaSyn = MetaSyn'
  module Timers : Timers_intf.TIMERS
end) : Strategy_intf.STRATEGY with module MetaSyn = StrategyRFS__1.MetaSyn'

module Strategy (Strategy__2 : sig
  module MetaGlobal : Meta_global.METAGLOBAL
  module MetaSyn' : Metasyn.METASYN
  module StrategyFRS : Strategy_intf.STRATEGY with module MetaSyn = MetaSyn'
  module StrategyRFS : Strategy_intf.STRATEGY with module MetaSyn = MetaSyn'
end) : Strategy_intf.STRATEGY with module MetaSyn = Strategy__2.MetaSyn'
