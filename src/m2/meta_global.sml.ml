open! Basis

(* Global parameters *)
(* Author: Carsten Schuermann *)
module MetaGlobal : METAGLOBAL = struct
  type strategy_ = Rfs | Frs

  let strategy = ref Frs
  let maxFill = ref 6
  let maxSplit = ref 2
  let maxRecurse = ref 10
end
(* structure MetaGlobal *)
