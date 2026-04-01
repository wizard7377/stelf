include module type of Prover_intf

module Prover (Prover__0 : sig
  module MetaGlobal : Meta_global.METAGLOBAL
  module MetaSyn' : Metasyn.METASYN
  module Init : Init_intf.INIT with module MetaSyn = MetaSyn'
  module Strategy : Strategy_intf.STRATEGY with module MetaSyn = MetaSyn'
  module Filling : Filling_intf.FILLING with module MetaSyn = MetaSyn'
  module Splitting : Splitting_intf.SPLITTING with module MetaSyn = MetaSyn'
  module Recursion : Recursion_intf.RECURSION with module MetaSyn = MetaSyn'
  module Qed : Qed_intf.QED with module MetaSyn = MetaSyn'
  module MetaPrint : Meta_print.METAPRINT with module MetaSyn = MetaSyn'
  module Names : NAMES

  (*! sharing Names.IntSyn = MetaSyn'.IntSyn !*)
  module Timers : Timers_intf.TIMERS
end) : PROVER
