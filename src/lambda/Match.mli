open Whnf_intf
open Unify_intf
include module type of Match_intf

module MakeMatch (Whnf : WHNF) (Unify : UNIFY) (Trail : TRAIL) : MATCH
