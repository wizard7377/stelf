include module type of Mtp_strategy_intf

module MTPStrategy (MTPStrategy__0 : sig
  module MTPGlobal : Mtp_global.MTPGLOBAL
  module StateSyn' : Statesyn_intf.STATESYN
  module MTPFilling : Mtp_filling_intf.MTPFILLING
  module MTPData : Mtp_data_intf.MTPDATA
  module MTPSplitting : Mtp_splitting_intf.MTPSPLITTING
  module MTPRecursion : Mtp_recursion_intf.MTPRECURSION
  module Inference : Inference_intf.INFERENCE
  module MTPrint : Mtp_print_intf.MTPRINT
  module Timers : Timers_intf.TIMERS
end) : MTPSTRATEGY
