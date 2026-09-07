open! Basis
open! Global.Global_
open! Timing
open! Table.Table_
open! Intsyn.Lambda_
open! Names.Names_
open! Paths
open! Print.Print_
open! Index.Index_
open! Subordinate
include module type of WORLDSYN

module WorldSyn (WorldSyn__0 : sig
  module Global : GLOBAL
  module Whnf : WHNF

  (*! sharing Whnf.IntSyn = IntSyn !*)
  module Index : INDEX

  (*! sharing Index.IntSyn = IntSyn !*)
  module Names : NAMES

  (*! sharing Names.IntSyn = IntSyn !*)
  module Unify : UNIFY

  (*! sharing Unify.IntSyn = IntSyn !*)
  module Abstract : ABSTRACT

  (*! sharing Abstract.IntSyn = IntSyn !*)
  module Constraints : CONSTRAINTS

  (*! sharing Constraints.IntSyn = IntSyn !*)
  (*! structure CsManager : CS_MANAGER !*)
  (*! sharing CsManager.IntSyn = IntSyn !*)
  module Subordinate : Subordinate_.SUBORDINATE

  (*! sharing Subordinate.IntSyn = IntSyn !*)
  module Print : PRINT

  (*! sharing Print.IntSyn = IntSyn !*)
  module Table : TABLE with type key = int

  (*! structure Paths : PATHS !*)
  module Origins : ORIGINS.ORIGINS

  (*! sharing Origins.Paths = Paths !*)
  (*! sharing Origins.IntSyn = IntSyn !*)
  module Timers : TIMERS.TIMERS
end) : WORLDSYN
