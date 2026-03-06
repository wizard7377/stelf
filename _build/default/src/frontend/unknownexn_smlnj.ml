# 1 "src/frontend/unknownexn_smlnj.sig.ml"

# 1 "src/frontend/unknownexn_smlnj.fun.ml"

# 1 "src/frontend/unknownexn_smlnj.sml.ml"
open! Basis;;
(* Print exception trace in unknownExn.  Both SML/NJ and MLton have
   SMLofNJ.exnHistory.
*);;
module UnknownExn = (UnknownExn)(struct
                                   let exnHistory = SMLofNJ.exnHistory;;
                                   end);;