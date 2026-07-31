open! Basis
open! Global
open! Global.Global_
open! Trail
open! Trail.Trail_
open! Table
open! Table.Table_
open WHNF
include module type of CONV

module Conv (Conv__0 : sig
  module Whnf : WHNF
end) : CONV
