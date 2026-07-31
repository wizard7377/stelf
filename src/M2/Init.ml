open! Basis
open! Stream
open! Stream.Stream_
open! Global
open! Global.Global_
open! Intsyn
open! Intsyn.Lambda_
open! Names
open! Names.Names_
open! Modes
open! Modes.Modes_
open! Paths
open! Paths.Paths_
open! Formatter
open! Formatter__Formatter_
open! Print
open! Print.Print_
open! Typecheck
open! Typecheck.Typecheck_
open! Terminate
open! Terminate.Terminate_
open! Index
open! Index.Index_
open! Thm
open! Thm.Thm_
open! Opsem
open! Opsem.Opsem_
open! Compile
open! Compile.Compile_
open! Subordinate
open! Subordinate
open! Table
open! Table.Table_
open! Timing
open! Timing.Timing_
open! Solvers
open! Solvers.Solvers_

(* # 1 "src/m2/Init.sig.ml" *)
open! Basis
open Metasyn

(* Initialization *)
(* Author: Carsten Schuermann *)
include INIT
(* signature INIT *)

(* # 1 "src/m2/Init.fun.ml" *)
open! Basis
open Metasyn
open MetaAbstract

(* Initialization *)
(* Author: Carsten Schuermann *)

exception Error of string

let () =
  Printexc.register_printer (function Error msg -> Some msg | _ -> None)

module Init (Init__0 : sig
  module MetaSyn' : Metasyn.METASYN
  module MetaAbstract : METAABSTRACT.METAABSTRACT with module MetaSyn = MetaSyn'
end) : INIT with module MetaSyn = Init__0.MetaSyn' = struct
  open Init__0
  module MetaSyn = MetaAbstract.MetaSyn

  exception Error = Error

  open! struct
    module M = MetaSyn
    module I = IntSyn

    let init' cid =
      let v_, _ = M.createAtomConst (I.Null, I.Const cid) in
      MetaAbstract.abstract
        (M.State
           ( ("/" ^ I.conDecName (I.sgnLookup cid)) ^ "/",
             M.Prefix (I.Null, I.Null, I.Null),
             v_ ))

    let init cidList = map init' cidList
  end

  (* init c = S'

       Invariant:
       If   c is type constant identifier
       then S' is initial prover State.
    *)
  (* init c1 .. cn = S1 .. Sn

       Invariant:
       If   c1 .. cn are mutually recursive
       then S1 .. Sn is an initial prover State.
    *)
  let init = init
end
(* local *)
(* functor Init *)

(* # 1 "src/m2/Init.sml.ml" *)
