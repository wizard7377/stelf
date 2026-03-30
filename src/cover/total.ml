(* # 1 "src/cover/total.sig.ml" *)
open! Basis

(* Total Declarations *)
(* Author: Frank Pfenning *)
module type TOTAL = sig
  (*! structure IntSyn : INTSYN !*)
  exception Error of string

  val reset : unit -> unit
  val install : IntSyn.cid -> unit

  (* install(a) --- a is total in its input arguments *)
  val uninstall : IntSyn.cid -> bool

  (* true: was known to be total *)
  val checkFam : IntSyn.cid -> unit
end

(* may raise Error(msg) *)
(* signature TOTAL *)

(* # 1 "src/cover/total.fun.ml" *)
open! Basis

(* Total Declarations *)
(* Author: Frank Pfenning *)

(* COVER module type inlined here to avoid dependency cycle with cover_ *)
module type COVER = sig
  exception Error of string

  val checkNoDef : IntSyn.cid -> unit
  val checkOut : IntSyn.dctx * IntSyn.eclo -> unit
  val checkCovers : IntSyn.cid * ModeSyn.modeSpine -> unit

  val coverageCheckCases :
    Tomega.worlds * (IntSyn.dctx * IntSyn.sub) list * IntSyn.dctx -> unit
end

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
  module Subordinate : SUBORDINATE

  (*! sharing Subordinate.IntSyn = IntSyn' !*)
  module Order : ORDER

  (*! sharing Order.IntSyn = IntSyn' !*)
  module Reduces : REDUCES

  (*! sharing Reduces.IntSyn = IntSyn' !*)
  module Cover : COVER

  (*! structure Paths : PATHS !*)
  module Origins : Origins.ORIGINS

  (*! sharing Origins.Paths = Paths !*)
  (*! sharing Origins.IntSyn = IntSyn' !*)
  module Timers : Timers.TIMERS
end) : TOTAL = struct
  (*! structure IntSyn = IntSyn' !*)
  exception Error of string

  module Table = Total__0.Table
  module Cover = Total__0.Cover
  module Order = Total__0.Order
  module Reduces = Total__0.Reduces
  module ModeTable = Total__0.ModeTable
  module ModeCheck = Total__0.ModeCheck
  module Origins = Total__0.Origins
  module Timers = Total__0.Timers

  open! struct
    module I = IntSyn
    module P = Paths
    module M = ModeSyn
    module N = Names

    let totalTable : unit Table.table = Table.new_ 0
    let rec reset () = Table.clear totalTable
    let rec install cid = Table.insert totalTable (cid, ())
    let rec lookup cid = Table.lookup totalTable cid
    let rec uninstall cid = Table.delete totalTable cid
  end

  (* totalTable (a) = SOME() iff a is total, otherwise NONE *)
  let reset = reset
  let install = install

  let uninstall = function
    | cid -> begin
        match lookup cid with
        | None -> false
        | Some _ -> begin
            uninstall cid;
            true
          end
      end

  let rec total cid =
    begin match lookup cid with None -> false | Some _ -> true
    end
  (* call only on constants *)

  exception Error' of P.occ * string

  (* copied from terminates/reduces.fun *)
  let rec error (c, occ, msg) =
    begin match Origins.originLookup c with
    | fileName, None -> raise (Error ((fileName ^ ":") ^ msg))
    | fileName, Some occDec ->
        raise
          (Error
             (P.wrapLoc'
                ( P.Loc (fileName, P.occToRegionDec occDec occ),
                  Origins.linesInfoLookup fileName,
                  msg )))
    end

  (* G is unused here *)
  let rec checkDynOrder = function
    | g_, vs_, 0, occ -> begin
        begin if !Global.chatter >= 5 then
          print
            "Output coverage: skipping redundant checking of third-order clause\n"
        else ()
        end;
        ()
      end
    | g_, vs_, n, occ -> checkDynOrderW (g_, Whnf.whnf vs_, n, occ)
  (* n > 0 *)
  (* Sun Jan  5 12:17:06 2003 -fp *)
  (* Functional calculus now checks this *)
  (* raise Error' (occ, ""Output coverage for clauses of order >= 3 not yet implemented"") *)

  and checkDynOrderW = function
    | g_, (I.Root _, s), n, occ -> ()
    | g_, (I.Pi (((I.Dec (_, v1_) as d1_), No), v2_), s), n, occ -> begin
        checkDynOrder (g_, (v1_, s), n - 1, P.label occ);
        checkDynOrder (I.Decl (g_, d1_), (v2_, I.dot1 s), n, P.body occ)
      end
    | g_, (I.Pi ((d1_, Maybe), v2_), s), n, occ ->
        checkDynOrder (I.Decl (g_, d1_), (v2_, I.dot1 s), n, P.body occ)

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
  let rec checkClause (g_, vs_, occ) = checkClauseW (g_, Whnf.whnf vs_, occ)

  and checkClauseW = function
    | g_, (I.Pi ((d1_, Maybe), v2_), s), occ ->
        let d1'_ = N.decEName (g_, I.decSub (d1_, s)) in
        checkClause (I.Decl (g_, d1'_), (v2_, I.dot1 s), P.body occ)
    | g_, (I.Pi (((I.Dec (_, v1_) as d1_), No), v2_), s), occ ->
        let _ = checkClause (I.Decl (g_, d1_), (v2_, I.dot1 s), P.body occ) in
        checkGoal (g_, (v1_, s), P.label occ)
    | g_, (I.Root _, s), occ -> ()
  (* clause head *)
  (* subgoal *)
  (* quantifier *)

  and checkGoal (g_, vs_, occ) = checkGoalW (g_, Whnf.whnf vs_, occ)

  and checkGoalW (g_, (v_, s), occ) =
    let a = I.targetFam v_ in
    let _ =
      begin if not (total a) then
        raise
          (Error'
             ( occ,
               ("Subgoal " ^ N.qidToString (N.constQid a))
               ^ " not declared to be total" ))
      else ()
      end
    in
    let _ = checkDynOrderW (g_, (v_, s), 2, occ) in
    try Cover.checkOut (g_, (v_, s))
    with Cover.Error msg ->
      raise (Error' (occ, "Totality: Output of subgoal not covered\n" ^ msg))
  (* can raise Cover.Error for third-order clauses *)

  (* checkDefinite (a, ms) = ()
       iff every mode in mode spine ms is either input or output
       Effect: raises Error (msg) otherwise
    *)
  let rec checkDefinite = function
    | a, M.Mnil -> ()
    | a, M.Mapp (M.Marg (M.Plus, _), ms') -> checkDefinite (a, ms')
    | a, M.Mapp (M.Marg (M.Minus, _), ms') -> checkDefinite (a, ms')
    | a, M.Mapp (M.Marg (M.Star, xOpt), ms') ->
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
        begin if !Global.chatter >= 4 then
          print (N.qidToString (N.constQid c) ^ " ")
        else ()
        end;
        begin
          begin if !Global.chatter >= 6 then print "\n" else ()
          end;
          begin try checkClause (I.Null, (I.constType c, I.id), P.top)
          with Error' (occ, msg) ->
            error (c, occ, msg);
            checkOutCover cs
          end
        end
      end
    | I.Def d :: cs -> begin
        begin if !Global.chatter >= 4 then
          print (N.qidToString (N.constQid d) ^ " ")
        else ()
        end;
        begin
          begin if !Global.chatter >= 6 then print "\n" else ()
          end;
          begin try checkClause (I.Null, (I.constType d, I.id), P.top)
          with Error' (occ, msg) ->
            error (d, occ, msg);
            checkOutCover cs
          end
        end
      end

  (* checkFam (a) = ()
       iff family a is total in its input arguments.
       This requires termination, input coverage, and local output coverage.
       Currently, there is no global output coverage.
       Effect: raises Error (msg) otherwise, where msg has filename and location.
    *)
  let rec checkFam a =
    let _ = Cover.checkNoDef a in
    let _ =
      try Subordinate.checkNoDef a
      with Subordinate.Error msg ->
        raise
          (Subordinate.Error
             ((("Totality checking " ^ N.qidToString (N.constQid a)) ^ ":\n")
             ^ msg))
      (* a cannot depend on type-level definitions *)
    in
    let _ =
      try
        begin
          Timers.time Timers.terminate Reduces.checkFam a;
          begin if !Global.chatter >= 4 then
            print (("Terminates: " ^ N.qidToString (N.constQid a)) ^ "\n")
          else ()
          end
        end
      with Reduces.Error msg -> raise (Reduces.Error msg)
    in
    let (Some ms) = ModeTable.modeLookup a in
    let _ = checkDefinite (a, ms) in
    let _ =
      try
        begin
          Timers.time Timers.coverage Cover.checkCovers (a, ms);
          begin if !Global.chatter >= 4 then
            print (("Covers (input): " ^ N.qidToString (N.constQid a)) ^ "\n")
          else ()
          end
        end
      with Cover.Error msg -> raise (Cover.Error msg)
    in
    let _ =
      begin if !Global.chatter >= 4 then
        print
          (("Output coverage checking family " ^ N.qidToString (N.constQid a))
          ^ "\n")
      else ()
      end
    in
    let _ = ModeCheck.checkFreeOut (a, ms) in
    let cs = Index.lookup a in
    let _ =
      try
        begin
          Timers.time Timers.coverage checkOutCover cs;
          begin
            begin if !Global.chatter = 4 then print "\n" else ()
            end;
            begin if !Global.chatter >= 4 then
              print (("Covers (output): " ^ N.qidToString (N.constQid a)) ^ "\n")
            else ()
            end
          end
        end
      with Cover.Error msg -> raise (Cover.Error msg)
    in
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

(* # 1 "src/cover/total.sml.ml" *)
