include module type of TOMEGATYPECHECK

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
  module Weaken : WEAKEN.WEAKEN
  module TomegaAbstract : TOMEGAABSTRACT.TOMEGAABSTRACT
end) : TOMEGATYPECHECK
