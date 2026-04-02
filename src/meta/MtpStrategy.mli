include module type of MtpStrategy_intf

module MTPStrategy (MTPStrategy__0 : sig
  module MTPGlobal : MtpGlobal.MTPGLOBAL
  module StateSyn' : Statesyn_intf.STATESYN
  module MTPFilling : MtpFilling_intf.MTPFILLING
  module MTPData : MtpData_intf.MTPDATA
  module MTPSplitting : MtpSplitting_intf.MTPSPLITTING
  module MTPRecursion : MtpRecursion_intf.MTPRECURSION
  module Inference : Inference_intf.INFERENCE
  module MTPrint : MtpPrint_intf.MTPRINT
  module Timers : Timers_intf.TIMERS
end) : MTPSTRATEGY
