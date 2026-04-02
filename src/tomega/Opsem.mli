include module type of Opsem_intf

module MakeOpsem (Opsem__0 : sig
  (* Internal syntax for functional proof term calculus *)
  (* Author: Carsten Schuermann, Adam Poswolsky *)
  module Whnf : WHNF
  module Abstract : ABSTRACT
  module Subordinate : Subordinate.Subordinate_.SUBORDINATE
  module TomegaTypeCheck : TomegaTypecheck_intf.TOMEGATYPECHECK
  module TomegaPrint : Tomegaprint.TOMEGAPRINT
  module Unify : UNIFY
end) : OPSEM
