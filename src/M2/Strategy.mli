include module type of STRATEGY

module StrategyFRS (StrategyFRS__0 : sig
  module MetaGlobal : METAGLOBAL.METAGLOBAL
  module MetaSyn' : Metasyn.METASYN
  module Filling : FILLING.FILLING with module MetaSyn = MetaSyn'
  module Splitting : SPLITTING.SPLITTING with module MetaSyn = MetaSyn'
  module Recursion : RECURSION.RECURSION with module MetaSyn = MetaSyn'
  module Lemma : LEMMA.LEMMA with module MetaSyn = MetaSyn'
  module Qed : QED.QED with module MetaSyn = MetaSyn'
  module MetaPrint : METAPRINT.METAPRINT with module MetaSyn = MetaSyn'
  module Timers : TIMERS.TIMERS
end) : STRATEGY.STRATEGY with module MetaSyn = StrategyFRS__0.MetaSyn'

module StrategyRFS (StrategyRFS__1 : sig
  module MetaGlobal : METAGLOBAL.METAGLOBAL
  module MetaSyn' : Metasyn.METASYN
  module Filling : FILLING.FILLING with module MetaSyn = MetaSyn'
  module Splitting : SPLITTING.SPLITTING with module MetaSyn = MetaSyn'
  module Recursion : RECURSION.RECURSION with module MetaSyn = MetaSyn'
  module Lemma : LEMMA.LEMMA with module MetaSyn = MetaSyn'
  module Qed : QED.QED with module MetaSyn = MetaSyn'
  module MetaPrint : METAPRINT.METAPRINT with module MetaSyn = MetaSyn'
  module Timers : TIMERS.TIMERS
end) : STRATEGY.STRATEGY with module MetaSyn = StrategyRFS__1.MetaSyn'

module Strategy (Strategy__2 : sig
  module MetaGlobal : METAGLOBAL.METAGLOBAL
  module MetaSyn' : Metasyn.METASYN
  module StrategyFRS : STRATEGY.STRATEGY with module MetaSyn = MetaSyn'
  module StrategyRFS : STRATEGY.STRATEGY with module MetaSyn = MetaSyn'
end) : STRATEGY.STRATEGY with module MetaSyn = Strategy__2.MetaSyn'
