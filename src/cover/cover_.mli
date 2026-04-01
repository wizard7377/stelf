include module type of Cover_intf

module MakeCover (Cover__0 : sig
  module Global : GLOBAL
  module Whnf : WHNF
  module Conv : CONV

  (*! sharing Whnf.IntSyn = IntSyn' !*)
  module Abstract : ABSTRACT

  (*! sharing Abstract.IntSyn = IntSyn' !*)
  module Unify : UNIFY

  (* must be trailing! *)
  (*! sharing Unify.IntSyn = IntSyn' !*)
  module Constraints : CONSTRAINTS

  (*! sharing Constraints.IntSyn = IntSyn' !*)
  module ModeTable : Modetable.MODETABLE
  module UniqueTable : Modetable.MODETABLE
  module Index : INDEX

  (*! sharing Index.IntSyn = IntSyn' !*)
  module Subordinate : Subordinate.Subordinate_.SUBORDINATE

  (*! sharing Subordinate.IntSyn = IntSyn' !*)
  module WorldSyn : Worldcheck_.WORLDSYN
  module Names : NAMES

  (*! sharing Names.IntSyn = IntSyn' !*)
  (*! structure Paths : PATHS !*)
  module Print : PRINT

  (*! sharing Print.IntSyn = IntSyn' !*)
  module TypeCheck : TYPECHECK

  (*! sharing TypeCheck.IntSyn = IntSyn' !*)
  (*! structure Cs_manager : CS_MANAGER !*)
  (*! sharing Cs_manager.IntSyn = IntSyn' !*)
  module Timers : Timers.TIMERS
end) : COVER

module Cover : COVER
module Total : Total_intf.TOTAL
