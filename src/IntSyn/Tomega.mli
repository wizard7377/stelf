open! Basis
open! Global
open! Global.Global_
open! Trail
open! Trail.Trail_
open! Table
open! Table.Table_
include module type of TOMEGA
module MakeTomega (Whnf : Whnf.WHNF) (Conv : Conv.CONV) : TOMEGA
module Tomega : TOMEGA
