(* # 1 "src/solvers/Solvers_.sig.ml" *)

(* # 1 "src/solvers/Solvers_.fun.ml" *)

(* # 1 "src/solvers/Solvers_.sml.ml" *)
open! Basis

module CsManager = CsManager
module Cs = Cs
module CsEqField = CsEqField
module CsIneqField = CsIneqField
module CsEqIntegers = CsEqIntegers
module CsIneqIntegers = CsIneqIntegers
module CsEqStrings = CsEqStrings
module CsEqBools = CsEqBools
module CsIntegersWord = CsIntegersWord

(*
structure CsManager = CsManager (structure Global = Global
                                 ! structure IntSyn = IntSyn !
                                 structure Unify = UnifyTrail
                                 structure Fixity = Names.Fixity
                                 structure ModeSyn = ModeSyn);
*)
module CSEqQ = CsEqField.CsEqField (struct
  module Field = Rationals_

  (*! structure IntSyn = IntSyn !*)
  module Whnf = Whnf
  module Unify = UnifyTrail
end)

(*! structure CsManager = CsManager !*)
module CSIneqQ = CsIneqField.CsIneqField (struct
  module OrderedField = Rationals_

  (*! structure IntSyn = IntSyn !*)
  module Trail = Trail
  module Unify = UnifyTrail
  module SparseArray = TableInstances.SparseArray
  module SparseArray2 = TableInstances.SparseArray2

  (*! structure CsManager = CsManager !*)
  module CsEqField = CSEqQ
end)

module CsEqStringsImpl = CsEqStrings.CsEqStrings (struct
  (*! structure IntSyn = IntSyn !*)
  module Whnf = Whnf
  module Unify = UnifyTrail
end)

(*! structure CsManager = CsManager !*)
module CsEqBoolsImpl = CsEqBools.CsEqBools (struct
  (*! structure IntSyn = IntSyn !*)
  module Whnf = Whnf
  module Unify = UnifyTrail
end)

(*! structure CsManager = CsManager !*)
module CSEqZ = CsEqIntegers.CsEqIntegers (struct
  module Integers = Integers_

  (*! structure IntSyn = IntSyn !*)
  module Whnf = Whnf
  module Unify = UnifyTrail
end)

(*! structure CsManager = CsManager !*)
module CSIneqZ = CsIneqIntegers.CsIneqIntegers (struct
  module Integers = Integers_
  module Rationals = Rationals_

  (*! structure IntSyn = IntSyn !*)
  module Trail = Trail
  module Unify = UnifyTrail
  module SparseArray = TableInstances.SparseArray
  module SparseArray2 = TableInstances.SparseArray2

  (*! structure CsManager = CsManager !*)
  module CsEqIntegers = CSEqZ
end)

module CSIntWord32 = CsIntegersWord.Cs_int_word (struct
  (*! structure IntSyn = IntSyn !*)
  module Whnf = Whnf
  module Unify = UnifyTrail

  (*! structure CsManager = CsManager !*)
  let wordSize = 32
end)
include Solvers_intf
(* execute for effect *)
(* wrapped in structure so it can be tracked by CM *)
module CSInstaller : CS_INSTALLER = struct
  let solvers =
    [
      CSEqQ.solver;
      CSIneqQ.solver;
      CsEqStringsImpl.solver;
      CsEqBoolsImpl.solver;
      CSEqZ.solver;
      CSIneqZ.solver;
      CSIntWord32.solver;
    ]

  let _ =
    List.app
      (function
        | s -> begin
            ignore (CsManager.installSolver s);
            ()
          end)
      solvers

  let version =
    List.foldr
      (function (s : CsManager.solver), str -> (s.name ^ "\n") ^ str)
      "" solvers
end
(*
  val _ = CsManager.installSolver (CSEqQ.solver)
  val _ = CsManager.installSolver (CSIneqQ.solver)
  val _ = CsManager.installSolver (CsEqStrings.solver)
  val _ = CsManager.installSolver (CsEqBools.solver)
  val _ = CsManager.installSolver (CSEqZ.solver)
  val _ = CsManager.installSolver (CSIneqZ.solver)
  val _ = CsManager.installSolver (CSIntWord32.solver)
  val version = ""12/19/2002""
  *)
