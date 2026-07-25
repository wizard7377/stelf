(* # 1 "src/solvers/Cs.sig.ml" *)
open! Basis

(* Constraint Solver *)

module type CS = sig
  (*! structure CsManager : CS_MANAGER !*)
  (* all a constraint solver must define is a structure
     suitable for the constraint solver manager to install.
  *)
  val solver : CsManager.solver
end
