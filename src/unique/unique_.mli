include module type of Unique_intf

module MakeUnique (Unique__0 : sig
  module Global : GLOBAL
  module Whnf : WHNF
  module Abstract : ABSTRACT
  module Unify : UNIFY

  (* must be trailing! *)
  module Constraints : CONSTRAINTS
  module UniqueTable : Modetable.MODETABLE
  module UniqueCheck : Modecheck.MODECHECK
  module Index : INDEX
  module Subordinate : Subordinate_.SUBORDINATE
  module WorldSyn : Worldcheck_.WORLDSYN
  module Names : NAMES
  module Print : PRINT
  module TypeCheck : TYPECHECK
  module Timers : Timers.TIMERS
end) : UNIQUE

module UniqueTable : Modetable.MODETABLE
module UniqueCheck : Modecheck.MODECHECK
module Unique : UNIQUE
