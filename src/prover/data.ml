(* # 1 "src/prover/data.sig.ml" *)
open! Basis

(* Data Global parameters *)
(* Author: Carsten Schuermann *)
include Data_intf
(* signature DATA *)

(* # 1 "src/prover/data.fun.ml" *)
open! Basis

(* Meta data parameters *)
(* Author: Carsten Schuermann *)
module Data : DATA = struct
  let maxFill = ref 5
  let maxSplit = ref 5
  let maxRecurse = ref 2
end
(* structure Data *)

(* # 1 "src/prover/data.sml.ml" *)
