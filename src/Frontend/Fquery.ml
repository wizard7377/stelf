open! Basis
open! Timing
open! Timing.Timing_
open! Stream
open! Stream.Stream_
open! Global
open! Global.Global_
open! Table
open! Table.Table_
open! Tabling
open! Intsyn
open! Intsyn.Lambda_
open! Names
open! Names.Names_
open! Paths
open! Paths.Paths_
open! Print
open! Print.Print_
open! Typecheck
open! Typecheck.Typecheck_
open! Style
open! Style.Style_
open! Modes
open! Modes.Modes_
open! Terminate
open! Terminate.Terminate_
open! Index
open! Index.Index_
open! Thm
open! Thm.Thm_
open! M2
open! M2.M2_
open! Compile
open! Compile.Compile_
open! Opsem
open! Opsem.Opsem_
open! Subordinate
open! Subordinate
open! Modules
open! Modules.Modules_
open! Meta
open! Meta.Meta_
open! Solvers
open! Solvers.Solvers_
open! Worldcheck
open! Worldcheck.Worldcheck_
open! Unique
open! Unique.Unique_
open! Cover
open! Cover.Cover_
open! Tomega_lib
open! Tomega_lib.Tomega_
open! Prover
open! Flit
open! Flit.Flit_
open! Msg
open! Msg.Msg_

(* # 1 "src/frontend/Fquery.sig.ml" *)
open! Basis

(* fquery: Executing logic programs via functional interpretation *)
(* Author: Carsten Schuermann *)
include FQUERY

(* may raise AbortQuery(msg) *)
(* signature SOLVE *)

(* # 1 "src/frontend/Fquery.fun.ml" *)
open! Basis

(* fquery: Executing logic programs via functional interpretation *)
(* Author: Carsten Schuermann *)
exception AbortQuery of string

let () =
  Printexc.register_printer (function AbortQuery msg -> Some msg | _ -> None)

module Fquery (Fquery__0 : sig
  module Global : GLOBAL
  module Names : NAMES
  module ReconQuery : RECONQUERY.RECON_QUERY
  module Timers : Timers.TIMERS
  module Print : PRINT
end) : FQUERY with module ExtQuery = Fquery__0.ReconQuery = struct
  module ExtQuery = Fquery__0.ReconQuery
  module ReconQuery = Fquery__0.ReconQuery
  module Timers = Fquery__0.Timers

  exception AbortQuery = AbortQuery

  module I = IntSyn
  module T = Tomega
  module W = WorldSyn
  module P = Paths

  (* evarInstToString Xs = msg
     formats instantiated EVars as a substitution.
     Abbreviate as empty string if chatter level is < 3.
  *)
  let evarInstToString xs_ =
    begin if !Global.chatter >= 3 then Print.evarInstToString xs_ else ""
    end

  (* expToString (G, U) = msg
     formats expression as a string.
     Abbreviate as empty string if chatter level is < 3.
  *)
  let expToString gu =
    begin if !Global.chatter >= 3 then Print.expToString gu else ""
    end

  let rec lower = function
    | 0, g_, v_ -> (g_, v_)
    | n, g_, I.Pi ((d_, _), v_) -> lower (n - 1, I.Decl (g_, d_), v_)

  let run (quy, Paths.Loc (fileName, r)) =
    let v_, optName, xs_ =
      ReconQuery.queryToQuery (quy, Paths.Loc (fileName, r))
    in
    ignore (Display.chatter_s 3 "%fquery");
    ignore (Display.chatter_s 3 " ");
    let _ =
      Display.chatter_s 3
        (Timers.time Timers.printing expToString (IntSyn.Null, v_) ^ ".\n")
    in
    let k, v1_ = Abstract.abstractDecImp v_ in
    let g_, v2_ = lower (k, I.Null, v1_) in
    let a = I.targetFam v2_ in
    let w_ = W.lookup a in
    let v3 = Worldify.worldifyGoal (g_, v2_) in
    ignore (TypeCheck.typeCheck (g_, (v3, I.Uni I.Type)));
    let p_ = Converter.convertGoal (T.embedCtx g_, v3) in
    let v_ = Timers.time Timers.delphin Opsem.evalPrg p_ in
    print (("Delphin: " ^ TomegaPrint.prgToString (I.Null, v_)) ^ "\n")
  (* optName = SOME(X) or NONE, Xs = free variables in query excluding X *)
  (* times itself *)
  (* G |- V'' : type *)
end
(* functor Solve *)

(* # 1 "src/frontend/Fquery.sml.ml" *)
