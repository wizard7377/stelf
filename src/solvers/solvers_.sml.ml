open! Basis

(*
structure Cs_manager = Cs_manager (structure Global = Global
                                 ! structure IntSyn = IntSyn !
                                 structure Unify = UnifyTrail
                                 structure Fixity = Names.Fixity
                                 structure ModeSyn = ModeSyn);
*)
module CSEqQ = Cs_eq_field.Cs_eq_field (struct
  module Field = Rationals_

  (*! structure IntSyn = IntSyn !*)
  module Whnf = Whnf
  module Unify = UnifyTrail
end)

(*! structure Cs_manager = Cs_manager !*)
module CSIneqQ = Cs_ineq_field.Cs_ineq_field (struct
  module OrderedField = Rationals_

  (*! structure IntSyn = IntSyn !*)
  module Trail = Trail
  module Unify = UnifyTrail
  module SparseArray = Table_instances.SparseArray
  module SparseArray2 = Table_instances.SparseArray2

  (*! structure Cs_manager = Cs_manager !*)
  module Cs_eq_field = CSEqQ
end)

module Cs_eq_strings = Cs_eq_strings.Cs_eq_strings (struct
  (*! structure IntSyn = IntSyn !*)
  module Whnf = Whnf
  module Unify = UnifyTrail
end)

(*! structure Cs_manager = Cs_manager !*)
module Cs_eq_bools = Cs_eq_bools.Cs_eq_bools (struct
  (*! structure IntSyn = IntSyn !*)
  module Whnf = Whnf
  module Unify = UnifyTrail
end)

(*! structure Cs_manager = Cs_manager !*)
module CSEqZ = Cs_eq_integers.Cs_eq_integers (struct
  module Integers = Integers_

  (*! structure IntSyn = IntSyn !*)
  module Whnf = Whnf
  module Unify = UnifyTrail
end)

(*! structure Cs_manager = Cs_manager !*)
module CSIneqZ = Cs_ineq_integers.Cs_ineq_integers (struct
  module Integers = Integers_
  module Rationals = Rationals_

  (*! structure IntSyn = IntSyn !*)
  module Trail = Trail
  module Unify = UnifyTrail
  module SparseArray = Table_instances.SparseArray
  module SparseArray2 = Table_instances.SparseArray2

  (*! structure Cs_manager = Cs_manager !*)
  module Cs_eq_integers = CSEqZ
end)

module CSIntWord32 = Cs_integers_word.Cs_int_word (struct
  (*! structure IntSyn = IntSyn !*)
  module Whnf = Whnf
  module Unify = UnifyTrail

  (*! structure Cs_manager = Cs_manager !*)
  let wordSize = 32
end)

module type CS_INSTALLER = sig
  val version : string
end

(* execute for effect *)
(* wrapped in structure so it can be tracked by CM *)
module CSInstaller : CS_INSTALLER = struct
  let solvers =
    [
      CSEqQ.solver;
      CSIneqQ.solver;
      Cs_eq_strings.solver;
      Cs_eq_bools.solver;
      CSEqZ.solver;
      CSIneqZ.solver;
      CSIntWord32.solver;
    ]

  let _ =
    List.app
      (function
        | s -> begin
            ignore (Cs_manager.installSolver s);
            ()
          end)
      solvers

  let version =
    List.foldr
      (function (s : Cs_manager.solver), str -> (s.name ^ "\n") ^ str)
      "" solvers
end
(*
  val _ = Cs_manager.installSolver (CSEqQ.solver)
  val _ = Cs_manager.installSolver (CSIneqQ.solver)
  val _ = Cs_manager.installSolver (Cs_eq_strings.solver)
  val _ = Cs_manager.installSolver (Cs_eq_bools.solver)
  val _ = Cs_manager.installSolver (CSEqZ.solver)
  val _ = Cs_manager.installSolver (CSIneqZ.solver)
  val _ = Cs_manager.installSolver (CSIntWord32.solver)
  val version = ""12/19/2002""
  *)
