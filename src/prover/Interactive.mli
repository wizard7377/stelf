include module type of Interactive_intf

module Interactive (Interactive__0 : sig
  (* Meta Prover Interface *)
  (* Author: Carsten Schuermann *)
  module Global : GLOBAL

  (*! structure IntSyn' : INTSYN !*)
  (*! structure Tomega' : TOMEGA !*)
  (*! sharing Tomega'.IntSyn = IntSyn' !*)
  module State' : State.STATE

  (*! sharing State'.IntSyn = IntSyn' !*)
  (*! sharing State'.Tomega = Tomega' !*)
  module Formatter : FORMATTER
  module Trail : TRAIL
  module Ring : Ring.RING
  module Names : NAMES

  (*! sharing Names.IntSyn = IntSyn' !*)
  module Weaken : Pweaken_intf.WEAKEN

  (*! sharing Weaken.IntSyn = IntSyn' !*)
  (* structure ModeSyn : MODESYN *)
  (*! sharing ModeSyn.IntSyn = IntSyn' !*)
  module WorldSyn : Worldcheck_.WORLDSYN

  (*! sharing WorldSyn.IntSyn = IntSyn' !*)
  (*! sharing WorldSyn.Tomega = Tomega' !*)
  module Introduce : Introduce_intf.INTRODUCE with module State = State'

  (*! sharing Introduce.IntSyn = IntSyn' !*)
  (*! sharing Introduce.Tomega = Tomega' !*)
  module Elim : Elim_intf.ELIM with module State = State'

  (*! sharing Elim.IntSyn = IntSyn' !*)
  (*! sharing Elim.Tomega = Tomega' !*)
  module Split : Split_intf.SPLIT with module State = State'

  (*! sharing Split.IntSyn = IntSyn' !*)
  (*! sharing Split.Tomega = Tomega' !*)
  module FixedPoint : Fixedpoint.FIXEDPOINT with module State = State'

  (*! sharing FixedPoint.IntSyn = IntSyn' !*)
  (*! sharing FixedPoint.Tomega = Tomega' !*)
  module Fill : Fill_intf.FILL with module State = State'
end) : INTERACTIVE
