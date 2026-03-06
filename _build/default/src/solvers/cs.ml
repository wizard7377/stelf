# 1 "src/solvers/cs.sig.ml"
open! Basis;;
(* Constraint Solver *);;
module type CS = sig
                 (*! structure CSManager : CS_MANAGER !*)
                 (* all a constraint solver must define is a structure
     suitable for the constraint solver manager to install.
  *)
                 val solver : CSManager.solver
                 end;;
(* signature CS *);;
# 1 "src/solvers/cs.fun.ml"

# 1 "src/solvers/cs.sml.ml"
