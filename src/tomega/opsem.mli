include module type of Opsem_intf

module Opsem (Opsem__0 : sig
  (* Internal syntax for functional proof term calculus *)
  (* Author: Carsten Schuermann, Adam Poswolsky *)
  module Whnf : WHNF
  module Abstract : ABSTRACT
  module Subordinate : Subordinate.Subordinate_.SUBORDINATE
  module TomegaTypeCheck : Tomega_typecheck.TOMEGATYPECHECK
  module TomegaPrint : Tomegaprint.TOMEGAPRINT
  module Unify : UNIFY
end) : OPSEM
