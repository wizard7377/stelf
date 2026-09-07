open! Global.Global_
open! Intsyn.Lambda_
open! Names.Names_
open! Paths
open! Paths.Paths_
open! Table.Table_
open! Modes
open! Terminate
open! Index.Index_
open! Timing

(* # 1 "src/cover/Total.sig.ml" *)

(* Total Declarations *)
(* Author: Frank Pfenning *)
include TOTAL

(* may raise Error(msg) *)
(* signature TOTAL *)

(* # 1 "src/cover/Total.fun.ml" *)
open! Basis

(* Total Declarations *)
(* Author: Frank Pfenning *)

exception Error of string

let () =
  Printexc.register_printer (function Error msg -> Some msg | _ -> None)

exception Error' of Paths.occ * string

let () =
  Printexc.register_printer (function Error' (_, msg) -> Some msg | _ -> None)

(* COVER module type inlined here to avoid dependency cycle with cover_ *)
module Total (Total__0 : sig
  module Global : GLOBAL
  module Table : TABLE with type key = int

  (*! structure IntSyn' : INTSYN !*)
  module Whnf : WHNF

  (*! sharing Whnf.IntSyn = IntSyn' !*)
  module Names : NAMES

  (*! sharing Names.IntSyn = IntSyn' !*)
  module ModeTable : Modetable.MODETABLE

  (*! sharing ModeSyn.IntSyn = IntSyn' !*)
  module ModeCheck : Modecheck.MODECHECK
  module Index : INDEX

  (*! sharing Index.IntSyn = IntSyn' !*)
  module Subordinate : Subordinate.Subordinate_.SUBORDINATE

  (*! sharing Subordinate.IntSyn = IntSyn' !*)
  module Order : ORDER

  (*! sharing Order.IntSyn = IntSyn' !*)
  module Reduces : REDUCES.REDUCES

  (*! sharing Reduces.IntSyn = IntSyn' !*)
  module Cover : COVER

  (*! structure Paths : PATHS !*)
  module Origins : Origins.ORIGINS

  (*! sharing Origins.Paths = Paths !*)
  (*! sharing Origins.IntSyn = IntSyn' !*)
  module Timers : Timers.TIMERS
end) : TOTAL = struct
  (*! structure IntSyn = IntSyn' !*)
  exception Error = Error

  module Table = Total__0.Table
  module Cover = Total__0.Cover
  module Order = Total__0.Order
  module Subordinate = Total__0.Subordinate
  module Reduces = Total__0.Reduces
  module ModeTable = Total__0.ModeTable
  module ModeCheck = Total__0.ModeCheck
  module Origins = Total__0.Origins
  module Timers = Total__0.Timers

  open! struct
    module I = IntSyn
    module P = Paths
    module M = Modes.Modesyn.ModeSyn
    module N = Names

    let totalTable : unit Table.table = Table.new_ 0
    let reset () = Table.clear totalTable
    let install cid = Table.insert totalTable (cid, ())
    let lookup cid = Table.lookup totalTable cid
    let uninstall cid = Table.delete totalTable cid
  end

  (* totalTable (a) = SOME() iff a is total, otherwise NONE *)
  let reset = reset
  let install = install

  let uninstall = function
    | cid ->
        begin match lookup cid with
        | None -> false
        | Some _ -> begin
            uninstall cid;
            true
          end
        end

  let total cid =
    begin match lookup cid with None -> false | Some _ -> true
    end
  (* call only on constants *)

  exception Error' = Error'

  (* copied from terminates/Reduces.fun *)
  let error (c, occ, msg) =
    begin match Origins.originLookup c with
    | fileName, None -> raise (Error ((fileName ^ ":") ^ msg))
    | fileName, Some occDec ->
        raise
          (Error
             (P.wrapLoc'
                (P.Loc (fileName, P.occToRegionDec occDec occ)) (Origins.linesInfoLookup fileName) msg))
    end

  (* G is unused here *)
  let rec checkDynOrder (g, vs, a, occ) = match a with
    | 0 -> begin
        Display.chatter_s 5
          "Output coverage: skipping redundant checking of third-order  clause\n";
        ()
      end
    | n -> checkDynOrderW (g, Whnf.whnf vs, n, occ)
  (* n > 0 *)
  (* Sun Jan  5 12:17:06 2003 -fp *)
  (* Functional calculus now checks this *)
  (* raise Error' (occ, ""Output coverage for clauses of order >= 3 not yet implemented"") *)

  and checkDynOrderW (g, a, n, occ) = match a with
    | (I.Root _, s) -> ()
    | (I.Pi (((I.Dec (_, v1) as d1), No), v2), s) -> begin
        checkDynOrder (g, (v1, s), n - 1, P.label occ);
        checkDynOrder (I.Decl (g, d1), (v2, I.dot1 s), n, P.body occ)
      end
    | (I.Pi ((d1, Maybe), v2), s) ->
        checkDynOrder (I.Decl (g, d1), (v2, I.dot1 s), n, P.body occ)

  (* static (= dependent) assumption --- consider only body *)
  (* dynamic (= non-dependent) assumption --- calculate dynamic order of V1 *)
  (* atomic subgoal *)

  (* checkClause (G, (V, s), occ) = ()
       checkGoal (G, (V, s), occ) = ()
       iff local output coverage for V is satisfied
           for clause V[s] or goal V[s], respectively.
       Effect: raises Error' (occ, msg) if coverage is not satisfied at occ.

       Invariants: G |- V[s] : type
    *)
  let rec checkClause (g, vs, occ) = checkClauseW (g, Whnf.whnf vs, occ)

  and checkClauseW (g, a, occ) = match a with
    | (I.Pi ((d1, Maybe), v2), s) ->
        let d1' = N.decEName g (I.decSub d1 s) in
        checkClause (I.Decl (g, d1'), (v2, I.dot1 s), P.body occ)
    | (I.Pi (((I.Dec (_, v1) as d1), No), v2), s) ->
        ignore (checkClause (I.Decl (g, d1), (v2, I.dot1 s), P.body occ));
        checkGoal (g, (v1, s), P.label occ)
    | (I.Root _, s) -> ()
  (* clause head *)
  (* subgoal *)
  (* quantifier *)

  and checkGoal (g, vs, occ) = checkGoalW (g, Whnf.whnf vs, occ)

  and checkGoalW (g, (v, s), occ) =
    let a = I.targetFam v in
    ignore begin if not (total a) then
        raise
          (Error'
             ( occ,
               ("Subgoal " ^ N.qidToString (N.constQid a))
               ^ " not declared to be total" ))
      else ()
      end;
    ignore (checkDynOrderW (g, (v, s), 2, occ));
    try Cover.checkOut g (v, s)
    with Cover.Error msg ->
      raise (Error' (occ, "Totality: Output of subgoal not covered\n" ^ msg))
  (* can raise Cover.Error for third-order clauses *)

  (* checkDefinite (a, ms) = ()
       iff every mode in mode spine ms is either input or output
       Effect: raises Error (msg) otherwise
    *)
  let rec checkDefinite (a, b) = match b with
    | M.Mnil -> ()
    | M.Mapp (M.Marg (M.Plus, _), ms') -> checkDefinite (a, ms')
    | M.Mapp (M.Marg (M.Minus, _), ms') -> checkDefinite (a, ms')
    | M.Mapp (M.Marg (M.Star, xOpt), ms') ->
        error
          ( a,
            P.top,
            ((("Error: Totality checking " ^ N.qidToString (N.constQid a))
             ^ ":\n")
            ^ "All argument modes must be input (+) or output (-)")
            ^ begin match xOpt with
            | None -> ""
            | Some x -> (" but argument " ^ x) ^ {| is indefinite (*)|}
            end )

  (* Fri Apr  5 19:25:54 2002 -fp *)
  (* Note: filename and location are missing in this error message *)

  (* checkOutCover [c1,...,cn] = ()
       iff local output coverage for every subgoal in ci:Vi is satisfied.
       Effect: raises Error (msg) otherwise, where msg has filename and location.
    *)
  let rec checkOutCover = function
    | [] -> ()
    | I.Const c :: cs -> begin
        Display.chatter_s 4 (N.qidToString (N.constQid c) ^ " ");
        begin
          Display.chatter_s 6 "\n";
          begin try checkClause (I.Null, (I.constType c, I.id), P.top)
          with Error' (occ, msg) ->
            error (c, occ, msg);
            checkOutCover cs
          end
        end
      end
    | I.Def d :: cs -> begin
        Display.chatter_s 4 (N.qidToString (N.constQid d) ^ " ");
        begin
          Display.chatter_s 6 "\n";
          begin try checkClause (I.Null, (I.constType d, I.id), P.top)
          with Error' (occ, msg) ->
            error (d, occ, msg);
            checkOutCover cs
          end
        end
      end

  (* checkFam (a) = ()
       iff family a is total in its input arguments.
       This requires termination, input coverage, and local output Coverage.
       Currently, there is no global output Coverage.
       Effect: raises Error (msg) otherwise, where msg has filename and location.
    *)
  let checkFam a =
    ignore (Cover.checkNoDef a);
    ignore (try Subordinate.checkNoDef a
      with Subordinate.Error msg ->
        raise
          (Subordinate.Error
             ((("Totality checking " ^ N.qidToString (N.constQid a)) ^ ":\n")
             ^ msg))
      (* a cannot depend on type-level definitions *));
    ignore (try
        begin
          Timers.time Timers.terminate Reduces.checkFam a;
          Display.chatter_s 4
            (("Terminates: " ^ N.qidToString (N.constQid a)) ^ "\n")
        end
      with Reduces.Error msg -> raise (Reduces.Error msg));
    let (Some ms) = ModeTable.modeLookup a in
    ignore (checkDefinite (a, ms));
    ignore (try
        begin
          Timers.time Timers.coverage (fun () -> Cover.checkCovers a ms) ();
          Display.chatter_s 4
            (("Covers (input): " ^ N.qidToString (N.constQid a)) ^ "\n")
        end
      with Cover.Error msg -> raise (Cover.Error msg));
    ignore (Display.chatter_s 4
        (("Output coverage checking family " ^ N.qidToString (N.constQid a))
        ^ "\n"));
    ignore (ModeCheck.checkFreeOut a ms);
    let cs = Index.lookup a in
    ignore (try
        begin
          Timers.time Timers.coverage checkOutCover cs;
          begin
            begin if !Global.chatter = 4 then print "\n" else ()
            end;
            Display.chatter_s 4
              (("Covers (output): " ^ N.qidToString (N.constQid a)) ^ "\n")
          end
        end
      with Cover.Error msg -> raise (Cover.Error msg));
    ()
  (* Ensuring that there is no bad interaction with type-level definitions *)
  (* a cannot be a type-level definition *)
  (* Checking termination *)
  (* Checking input coverage *)
  (* by termination invariant, there must be consistent mode for a *)
  (* must be defined and well-moded *)
  (* all arguments must be either input or output *)
  (* Checking output coverage *)
  (* all variables in output args must be free *)
end
(* functor Total *)

(* # 1 "src/cover/Total.sml.ml" *)
