include module type of Style_intf

module MakeStyleCheck
    (Whnf : WHNF)
    (Index : INDEX)
    (Origins : Origins.ORIGINS) :
  STYLECHECK

module StyleCheck : STYLECHECK
