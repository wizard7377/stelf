# 1 "src/solvers/solvers_.sig.ml"

# 1 "src/solvers/solvers_.fun.ml"

# 1 "src/solvers/solvers_.sml.ml"
open! Basis;;
(* now in cs-manager.fun *);;
(*
structure CSManager = CSManager (structure Global = Global
                                 ! structure IntSyn = IntSyn !
                                 structure Unify = UnifyTrail
                                 structure Fixity = Names.Fixity
                                 structure ModeSyn = ModeSyn);
*);;
module CSEqQ = (CSEqField)(struct
                             module Field = Rationals;;
                             (*! structure IntSyn = IntSyn !*);;
                             module Whnf = Whnf;;
                             module Unify = UnifyTrail;;
                             end);;
(*! structure CSManager = CSManager !*);;
module CSIneqQ = (CSIneqField)(struct
                                 module OrderedField = Rationals;;
                                 (*! structure IntSyn = IntSyn !*);;
                                 module Trail = Trail;;
                                 module Unify = UnifyTrail;;
                                 module SparseArray = SparseArray;;
                                 module SparseArray2 = SparseArray2;;
                                 (*! structure CSManager = CSManager !*);;
                                 module CSEqField = CSEqQ;;
                                 module Compat = Compat;;
                                 end);;
module CSEqStrings = (CSEqStrings)(struct
                                     (*! structure IntSyn = IntSyn !*);;
                                     module Whnf = Whnf;;
                                     module Unify = UnifyTrail;;
                                     end);;
(*! structure CSManager = CSManager !*);;
module CSEqBools = (CSEqBools)(struct
                                 (*! structure IntSyn = IntSyn !*);;
                                 module Whnf = Whnf;;
                                 module Unify = UnifyTrail;;
                                 end);;
(*! structure CSManager = CSManager !*);;
module CSEqZ = (CSEqIntegers)(struct
                                module Integers = Integers;;
                                (*! structure IntSyn = IntSyn !*);;
                                module Whnf = Whnf;;
                                module Unify = UnifyTrail;;
                                end);;
(*! structure CSManager = CSManager !*);;
module CSIneqZ = (CSIneqIntegers)(struct
                                    module Integers = Integers;;
                                    module Rationals = Rationals;;
                                    (*! structure IntSyn = IntSyn !*);;
                                    module Trail = Trail;;
                                    module Unify = UnifyTrail;;
                                    module SparseArray = SparseArray;;
                                    module SparseArray2 = SparseArray2;;
                                    (*! structure CSManager = CSManager !*);;
                                    module CSEqIntegers = CSEqZ;;
                                    module Compat = Compat;;
                                    end);;
module CSIntWord32 = (CSIntWord)(struct
                                   (*! structure IntSyn = IntSyn !*);;
                                   module Whnf = Whnf;;
                                   module Unify = UnifyTrail;;
                                   (*! structure CSManager = CSManager !*);;
                                   let wordSize = 32;;
                                   end);;
module type CS_INSTALLER = sig val version : string end;;
(* execute for effect *);;
(* wrapped in structure so it can be tracked by CM *);;
module CSInstaller : CS_INSTALLER =
  struct
    let solvers =
      [CSEqQ.solver; CSIneqQ.solver; CSEqStrings.solver; CSEqBools.solver;
       CSEqZ.solver; CSIneqZ.solver; CSIntWord32.solver];;
    let _ =
      List.app
      (function 
                | s -> begin
                         CSManager.installSolver s;()
                         end)
      solvers;;
    let version =
      List.foldr
      (function 
                | (s, str) -> (((fun r -> r.name) s) ^ "\n") ^ str)
      ""
      solvers;;
    end;;
(*
  val _ = CSManager.installSolver (CSEqQ.solver)
  val _ = CSManager.installSolver (CSIneqQ.solver)
  val _ = CSManager.installSolver (CSEqStrings.solver)
  val _ = CSManager.installSolver (CSEqBools.solver)
  val _ = CSManager.installSolver (CSEqZ.solver)
  val _ = CSManager.installSolver (CSIneqZ.solver)
  val _ = CSManager.installSolver (CSIntWord32.solver)
  val version = ""12/19/2002""
  *);;