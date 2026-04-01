(* # 1 "src/worldcheck/worldcheck_.sig.ml" *)

(* # 1 "src/worldcheck/worldcheck_.fun.ml" *)

(* # 1 "src/worldcheck/worldcheck_.sml.ml" *)
open! Basis

module type WORLDIFY = Worldify_intf.WORLDIFY
module type WORLDSYN = WorldSyn_intf.WORLDSYN

module WorldSyn : WORLDSYN
module Worldify : WORLDIFY
