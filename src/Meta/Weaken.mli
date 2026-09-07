open! Intsyn.Lambda_
include module type of WEAKEN
module Make_Weaken (Whnf : WHNF) : WEAKEN.WEAKEN
