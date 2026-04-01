include module type of Mpi_intf

module Mpi (Mpi__0 : sig
  module MetaGlobal : Meta_global.METAGLOBAL
  module MetaSyn' : Metasyn.METASYN
  module Init : Init_intf.INIT with module MetaSyn = MetaSyn'
  module Filling : Filling_intf.FILLING with module MetaSyn = MetaSyn'
  module Splitting : Splitting_intf.SPLITTING with module MetaSyn = MetaSyn'
  module Recursion : Recursion_intf.RECURSION with module MetaSyn = MetaSyn'
  module Lemma : Lemma_intf.LEMMA with module MetaSyn = MetaSyn'
  module Strategy : Strategy_intf.STRATEGY with module MetaSyn = MetaSyn'
  module Qed : Qed_intf.QED with module MetaSyn = MetaSyn'
  module MetaPrint : Meta_print.METAPRINT with module MetaSyn = MetaSyn'
  module Names : NAMES

  (*! sharing Names.IntSyn = MetaSyn'.IntSyn !*)
  module Timers : Timers_intf.TIMERS
  module Ring : Ring_intf.RING
end) : MPI with module MetaSyn = Mpi__0.MetaSyn'
