include module type of Style_intf

module MakeStyleCheck (StyleCheck__0 : sig
  (* Style Checking *)
  (* Author: Carsten Schuermann *)
  module Whnf : WHNF
  module Index : INDEX
  module Origins : Origins.ORIGINS
end) : STYLECHECK

module StyleCheck : STYLECHECK
