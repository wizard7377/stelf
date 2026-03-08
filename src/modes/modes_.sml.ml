open! Basis

(* structure ModeSyn  in modesyn.sml *)
module ModeSyn = Modesyn.ModeSyn

module ModeTable = Modetable.MakeModeTable (struct
  module Table = Table_instances.IntRedBlackTree
end)

module ModeDec = Modedec.MakeModeDec (struct end)

(*! structure ModeSyn' = ModeSyn !*)
(*! structure Paths' = Paths !*)
module ModeCheck = Modecheck.MakeModeCheck (struct
  (*! structure IntSyn = IntSyn !*)
  module ModeTable = ModeTable
  module Whnf = Whnf
  module Index = Index

  (*! structure Paths = Paths !*)
  module Origins = Origins
end)

module ModePrint = Modeprint.MakeModePrint (struct
  (*! structure ModeSyn' = ModeSyn !*)
  module Names = Names
  module Formatter = Formatter
  module Print = Print
end)
