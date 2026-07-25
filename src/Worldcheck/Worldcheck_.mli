(* # 1 "src/worldcheck/Worldcheck_.sig.ml" *)

(* # 1 "src/worldcheck/Worldcheck_.fun.ml" *)

(* # 1 "src/worldcheck/Worldcheck_.sml.ml" *)
open! Basis

module type WORLDIFY = WORLDIFY.WORLDIFY
module type WORLDSYN = WORLDSYN.WORLDSYN

module WorldSyn : WORLDSYN
module Worldify : WORLDIFY
