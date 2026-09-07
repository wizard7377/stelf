open! Intsyn.Lambda_
open! Paths
open! Index.Index_
include module type of STYLE

module MakeStyleCheck
    (Whnf : WHNF)
    (Index : INDEX)
    (Origins : Origins.ORIGINS) : STYLECHECK

module StyleCheck : STYLECHECK
