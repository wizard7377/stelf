# 1 "src/server/mlton_thread.sig.ml"

# 1 "src/server/mlton_thread.fun.ml"

# 1 "src/server/mlton_thread.sml.ml"
open! Basis;;
(* Construct a 20041109-workalike MLton.Thread for previous MLton versions *);;
module MLton = struct
                 open MLton;;
                 module Thread = struct
                                   open MLton.Thread;;
                                   let rec prepare (f, x) = f;;
                                   end;;
                 end;;