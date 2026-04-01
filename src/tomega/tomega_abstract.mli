include module type of Tomega_abstract_intf

module TomegaAbstract (TomegaAbstract__0 : sig
  (* Converter from relational representation to a functional
   representation of proof terms *)
  (* Author: Carsten Schuermann *)
  module Global : GLOBAL

  val abstract_raiseType : IntSyn.dctx * IntSyn.exp -> IntSyn.exp
  val abstract_raiseTerm : IntSyn.dctx * IntSyn.exp -> IntSyn.exp

  module Whnf : WHNF
  module Subordinate : Subordinate.Subordinate_.SUBORDINATE
end) : TOMEGAABSTRACT
