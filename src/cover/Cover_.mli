include module type of Cover_intf

module MakeCover
    (Global : GLOBAL)
    (Whnf : WHNF)
    (Conv : CONV)
    (Abstract : ABSTRACT)
    (Unify : UNIFY)
    (Constraints : CONSTRAINTS)
    (ModeTable : Modetable.MODETABLE)
    (UniqueTable : Modetable.MODETABLE)
    (Index : INDEX)
    (Subordinate : Subordinate.Subordinate_.SUBORDINATE)
    (WorldSyn : Worldcheck_.WORLDSYN)
    (Names : NAMES)
    (Print : PRINT)
    (TypeCheck : TYPECHECK)
    (Timers : Timers.TIMERS) :
  COVER
(*
  (* must be trailing! Constraints *)
  (*! sharing Whnf.IntSyn = IntSyn' !*)
  (*! sharing Abstract.IntSyn = IntSyn' !*)
  (*! sharing Unify.IntSyn = IntSyn' !*)
  (*! sharing Constraints.IntSyn = IntSyn' !*)
  (*! sharing Index.IntSyn = IntSyn' !*)
  (*! sharing Subordinate.IntSyn = IntSyn' !*)
  (*! sharing Names.IntSyn = IntSyn' !*)
  (*! sharing Print.IntSyn = IntSyn' !*)
  (*! sharing TypeCheck.IntSyn = IntSyn' !*)
*)

module Cover : COVER
module Total : Total_intf.TOTAL
