open Whnf_intf
include module type of Unify_intf

module MakeUnify (Whnf : WHNF) (Trail : TRAIL) : UNIFY
