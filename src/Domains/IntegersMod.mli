(* # 1 "src/domains/IntegersMod.sig.ml" *)

(* # 1 "src/domains/IntegersMod.fun.ml" *)
open Basis
open Field

(* Integers Modulo a Prime Number *)
(* Author: Roberto Virga *)

module IntegersMod (IntegersMod__0 : sig
  val p : int
end) : FIELD
