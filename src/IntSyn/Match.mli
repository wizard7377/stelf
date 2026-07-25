open WHNF
open UNIFY
include module type of MATCH
module MakeMatch (Whnf : WHNF) (Unify : UNIFY) (Trail : TRAIL) : MATCH
