include module type of Normalize_intf

module Normalize (Normalize__0 : sig
  (* Internal syntax for functional proof term calculus *)
  (* Author: Carsten Schuermann *)
  module Whnf : WHNF
end) : NORMALIZE
