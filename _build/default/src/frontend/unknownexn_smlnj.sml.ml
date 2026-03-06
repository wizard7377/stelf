open! Basis;;
(* Print exception trace in unknownExn.  Both SML/NJ and MLton have
   SMLofNJ.exnHistory.
*);;
module UnknownExn = (UnknownExn)(struct
                                   let exnHistory = SMLofNJ.exnHistory;;
                                   end);;