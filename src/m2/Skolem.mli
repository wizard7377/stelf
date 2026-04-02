include module type of Skolem_intf

module Skolem (Skolem__0 : sig
  (* Skolem constant administration *)
  (* Author: Carsten Schuermann *)
  module Global : GLOBAL

  (*! structure IntSyn' : INTSYN !*)
  module Whnf : WHNF

  (*! sharing Whnf.IntSyn = IntSyn' !*)
  module Abstract : ABSTRACT

  (*! sharing Abstract.IntSyn = IntSyn' !*)
  module IndexSkolem : INDEX

  (*! sharing IndexSkolem.IntSyn = IntSyn' !*)
  module ModeTable : Modetable.MODETABLE

  (*! sharing Modes.Modesyn.ModeSyn.IntSyn = IntSyn' !*)
  module Print : PRINT

  (*! sharing Print.IntSyn = IntSyn' !*)
  module Compile : COMPILE

  (*! sharing Compile.IntSyn = IntSyn' !*)
  module Timers : Timers_intf.TIMERS
  module Names : NAMES
end) : SKOLEM
