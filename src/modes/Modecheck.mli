include module type of Modecheck_intf

module MakeModeCheck
    (ModeTable : Modetable.MODETABLE)
    (Whnf : WHNF)
    (Index : INDEX)
    (Origins : Origins.ORIGINS) :
  MODECHECK
