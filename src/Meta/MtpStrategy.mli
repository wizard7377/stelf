include module type of MTPSTRATEGY

module MTPStrategy (MTPStrategy__0 : sig
  module MTPGlobal : MtpGlobal.MTPGLOBAL
  module StateSyn' : STATESYN.STATESYN
  module MTPFilling : MTPFILLING.MTPFILLING
  module MTPData : MTPDATA.MTPDATA
  module MTPSplitting : MTPSPLITTING.MTPSPLITTING
  module MTPRecursion : MTPRECURSION.MTPRECURSION
  module Inference : INFERENCE.INFERENCE
  module MTPrint : MTPPRINT.MTPRINT
  module Timers : TIMERS.TIMERS
end) : MTPSTRATEGY
