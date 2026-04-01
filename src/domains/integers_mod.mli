(* # 1 "src/domains/integers_mod.sig.ml" *)

(* # 1 "src/domains/integers_mod.fun.ml" *)
open Basis
open Field

(* Integers Modulo a Prime Number *)
(* Author: Roberto Virga *)

module IntegersMod (IntegersMod__0 : sig
  val p : int
end) : FIELD
