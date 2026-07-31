open! Basis
open! Global
open! Global.Global_
open! Trail
open! Trail.Trail_
open! Table
open! Table.Table_
open WHNF
include module type of UNIFY
module MakeUnify (Whnf : WHNF) (Trail : TRAIL) : UNIFY
