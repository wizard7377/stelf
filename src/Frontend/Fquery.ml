open! Timing
open! Global.Global_
open! Intsyn.Lambda_
open! Names.Names_
open! Paths.Paths_
open! Print.Print_
open! Typecheck.Typecheck_
open! Worldcheck.Worldcheck_
open! Tomega_lib.Tomega_

(* # 1 "src/frontend/Fquery.sig.ml" *)

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
  let evarInstToString xs =
    begin if !Global.chatter >= 3 then Print.evarInstToString xs else ""
    end

  (* expToString (G, U) = msg
     formats expression as a string.
     Abbreviate as empty string if chatter level is < 3.
  *)
  let expToString gu =
    begin if !Global.chatter >= 3 then (let g__, u__ = gu in Print.expToString g__ u__) else ""
    end

  let rec lower (n, g, a) = match n, a with
    | 0, v -> (g, v)
    | n, I.Pi ((d, _), v) -> lower (n - 1, I.Decl (g, d), v)

  let run quy (Paths.Loc (fileName, r)) =
    let v, optName, xs =
      ReconQuery.queryToQuery quy (Paths.Loc (fileName, r))
    in
    ignore (Display.chatter_s 3 "%fquery");
    ignore (Display.chatter_s 3 " ");
    ignore (Display.chatter_s 3
        (Timers.time Timers.printing expToString (IntSyn.Null, v) ^ ".\n"));
    let k, v1 = Abstract.abstractDecImp v in
    let g, v2 = lower (k, I.Null, v1) in
    let a = I.targetFam v2 in
    let w = W.lookup a in
    let v3 = Worldify.worldifyGoal g v2 in
    ignore (TypeCheck.typeCheck g (v3, I.Uni I.Type));
    let p = Converter.convertGoal (T.embedCtx g) v3 in
    let v = Timers.time Timers.delphin Opsem.evalPrg p in
    print (("Delphin: " ^ TomegaPrint.prgToString I.Null v) ^ "\n")
  (* optName = SOME(X) or NONE, Xs = free variables in query excluding X *)
  (* times itself *)
  (* G |- V'' : type *)
end
(* functor Solve *)

(* # 1 "src/frontend/Fquery.sml.ml" *)
