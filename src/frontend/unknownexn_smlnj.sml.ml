open! Basis
open Smlofnj
(* Print exception trace in unknownExn.  Both SML/NJ and MLton have
   SMLofNJ.exnHistory.
*)
module UnknownExn = Unknownexn.MakeUnknownExn (struct
  let exnHistory = SMLofNJ.exnHistory
end)
