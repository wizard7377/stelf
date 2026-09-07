open! Intsyn.Lambda_
open! Paths
open! Index.Index_
include module type of MODECHECK

module MakeModeCheck
    (ModeTable : Modetable.MODETABLE)
    (Whnf : WHNF)
    (Index : INDEX)
    (Origins : Origins.ORIGINS) : MODECHECK
