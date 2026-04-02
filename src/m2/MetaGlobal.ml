(* # 1 "src/m2/MetaGlobal.sig.ml" *)
open! Basis

(* Global parameters *)
(* Author: Carsten Schuermann *)
include MetaGlobal_intf
(* signature METAGLOBAL *)

(* # 1 "src/m2/MetaGlobal.fun.ml" *)

(* # 1 "src/m2/MetaGlobal.sml.ml" *)
open! Basis

(* Global parameters *)
(* Author: Carsten Schuermann *)
module MetaGlobal : METAGLOBAL = struct
  type strategy = Rfs | Frs [@@deriving eq, ord, show]

  let strategy = ref Frs
  let maxFill = ref 6
  let maxSplit = ref 2
  let maxRecurse = ref 10
end
(* structure MetaGlobal *)
