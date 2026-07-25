include module type of INTRODUCE

module Introduce (Introduce__0 : sig
  (* Introduce *)
  (* Author: Carsten Schuermann *)
  (*! structure IntSyn' : INTSYN !*)
  (*! structure Tomega' : TOMEGA !*)
  (*! sharing Tomega'.IntSyn = IntSyn' !*)
  module State' : State.STATE
  module TomegaNames : Tomeganames.TOMEGANAMES
end) : INTRODUCE with module State = Introduce__0.State'
