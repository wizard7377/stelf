open! Basis
open! Global
open! Global.Global_
open! Trail
open! Trail.Trail_
open! Table
open! Table.Table_
open WHNF
open UNIFY
include module type of MATCH
module MakeMatch (Whnf : WHNF) (Unify : UNIFY) (Trail : TRAIL) : MATCH
