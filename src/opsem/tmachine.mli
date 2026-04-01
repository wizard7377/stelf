(* # 1 "src/opsem/tmachine.sig.ml" *)

(* # 1 "src/opsem/tmachine.fun.ml" *)
open! Index
open! Trace
open! Absmachine
open! Basis

(* Abstract Machine for Tracing *)
(* Author: Frank Pfenning *)
(* Modified: Jeff Polakow, Frank Pfenning, Larry Greenfield, Roberto Virga *)

module TMachine (TMachine__0 : sig
  (*! structure IntSyn' : INTSYN !*)
  (*! structure CompSyn' : COMPSYN !*)
  (*! sharing CompSyn'.IntSyn = IntSyn' !*)
  module Unify : UNIFY

  (*! sharing Unify.IntSyn = IntSyn' !*)
  module Assign : ASSIGN

  (*! sharing Assign.IntSyn = IntSyn' !*)
  module Index : INDEX

  (*! sharing Index.IntSyn = IntSyn' !*)
  module CPrint : Cprint.CPRINT

  (*! sharing CPrint.IntSyn = IntSyn' !*)
  (*! sharing CPrint.CompSyn = CompSyn' !*)
  module Names : NAMES

  (*! sharing Names.IntSyn = IntSyn' !*)
  (*! structure Cs_manager : CS_MANAGER !*)
  (*! sharing Cs_manager.IntSyn = IntSyn' !*)
  module Trace : TRACE
end) : ABSMACHINE
