# 1 "src/server/sigint.sig.ml"
open! Basis;;
module type SIGINT = sig val interruptLoop : (unit -> unit) -> unit end;;
(* signature SIGINT *);;
# 1 "src/server/sigint.fun.ml"

# 1 "src/server/sigint.sml.ml"
