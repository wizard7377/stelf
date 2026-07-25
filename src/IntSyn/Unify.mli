open WHNF
include module type of UNIFY
module MakeUnify (Whnf : WHNF) (Trail : TRAIL) : UNIFY
