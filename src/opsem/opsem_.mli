(* # 1 "src/opsem/opsem_.sig.ml" *)

(* # 1 "src/opsem/opsem_.fun.ml" *)

(* # 1 "src/opsem/opsem_.sml.ml" *)
open! Basis

module AbsMachine : Absmachine.ABSMACHINE
module PtRecon : Ptrecon.PTRECON
module AbsMachineSbt : Absmachine_sbt.ABSMACHINESBT
module Tabled_ : Tabled_machine.TABLED
module SwMachine : Absmachine.ABSMACHINE
module Trace : Trace_intf.TRACE
