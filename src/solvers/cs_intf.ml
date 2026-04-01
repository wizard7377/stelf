(* # 1 "src/solvers/cs.sig.ml" *)
open! Basis

(* Constraint Solver *)

module type CS = sig
  (*! structure Cs_manager : CS_MANAGER !*)
  (* all a constraint solver must define is a structure
     suitable for the constraint solver manager to install.
  *)
  val solver : Cs_manager.solver
end
