include module type of Unique_intf

module MakeUnique
    (Global : GLOBAL)
    (Whnf : WHNF)
    (Abstract : ABSTRACT)
    (Unify : UNIFY)
    (Constraints : CONSTRAINTS)
    (UniqueTable : Modetable.MODETABLE)
    (UniqueCheck : Modecheck.MODECHECK)
    (Index : INDEX)
    (Subordinate : Subordinate_.SUBORDINATE)
    (WorldSyn : Worldcheck_.WORLDSYN)
    (Names : NAMES)
    (Print : PRINT)
    (TypeCheck : TYPECHECK)
    (Timers : Timers.TIMERS) :
  UNIQUE
(* must be trailing: Constraints *)

module UniqueTable : Modetable.MODETABLE
module UniqueCheck : Modecheck.MODECHECK
module Unique : UNIQUE
