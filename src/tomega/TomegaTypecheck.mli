include module type of TomegaTypecheck_intf

module TomegaTypeCheck (TomegaTypeCheck__0 : sig
  (* Type checking for Tomega *)
  (* Author: Carsten Schuermann *)
  (* Modified: Yu Liao *)
  module Abstract : ABSTRACT
  module TypeCheck : TYPECHECK
  module Conv : CONV
  module Whnf : WHNF
  module Print : PRINT
  module TomegaPrint : Tomegaprint.TOMEGAPRINT
  module Subordinate : Subordinate.Subordinate_.SUBORDINATE
  module Weaken : Weaken_intf.WEAKEN
  module TomegaAbstract : TomegaAbstract_intf.TOMEGAABSTRACT
end) : TOMEGATYPECHECK
