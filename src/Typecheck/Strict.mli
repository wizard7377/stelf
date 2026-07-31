open! Basis
open! Intsyn
open! Intsyn.Lambda_
open! Print
open! Print.Print_
open! Paths
open! Paths.Paths_
open! Names
open! Names.Names_
include module type of STRICT

module Strict (Strict__0 : sig
  module Whnf : WHNF
end) : STRICT
