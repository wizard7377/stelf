open! Basis
open! Global
open! Global.Global_
open! Trail
open! Trail.Trail_
open! Table
open! Table.Table_
include module type of ABSTRACT

module MakeAbstract
    (Whnf : Whnf.WHNF)
    (Unify : Unify.UNIFY)
    (Constraints : Constraints.CONSTRAINTS) : ABSTRACT
