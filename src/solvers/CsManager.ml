(* # 1 "src/solvers/CsManager.sig.ml" *)
open! Basis

(* Constraint Solver Manager *)
(* Author: Roberto Virga *)
include CsManager_intf
(* signature CS_MANAGER *)

(* # 1 "src/solvers/CsManager.fun.ml" *)
open! Basis

(* Constraint Solver Manager *)
(* Author: Roberto Virga *)
module MakeCsManager (CSManager__0 : sig
  module Global : GLOBAL

  (*! structure IntSyn : INTSYN !*)
  module Unify : UNIFY

  (*! sharing Unify.IntSyn = IntSyn !*)
  module Fixity : FIXITY
end) : CS_MANAGER with module Fixity = CSManager__0.Fixity = struct
  module IntSyn = IntSyn
  module Fixity = CSManager__0.Fixity

  (* structure ModeSyn = ModeSyn *)
  type nonrec sigEntry =
    IntSyn.conDec * Fixity.fixity option * ModeSyn.modeSpine list

  (* global signature entry *)
  (* constant declaration plus optional precedence and mode information *)
  type nonrec __0 = { parse : string -> IntSyn.conDec option }
  type nonrec fgnConDec = __0

  (* foreign constant declaration *)
  type nonrec __1 = {
    name : string;
    keywords : string;
    needs : string list;
    fgnConst : fgnConDec option;
    init : int * (sigEntry -> IntSyn.cid) -> unit;
    reset : unit -> unit;
    mark : unit -> unit;
    unwind : unit -> unit;
  }

  type nonrec solver = __1

  (* constraint solver *)
  exception Error of string

  open! struct
    let emptySolver =
      {
        name = "";
        keywords = "";
        needs = [];
        fgnConst = None;
        init = (function _ -> ());
        reset = (function () -> ());
        mark = (function () -> ());
        unwind = (function () -> ());
      }

    let unifySolver =
      {
        name = "Unify";
        keywords = "unification";
        needs = [];
        fgnConst = None;
        init = (function _ -> ());
        reset = CSManager__0.Unify.reset;
        mark = CSManager__0.Unify.mark;
        unwind = CSManager__0.Unify.unwind;
      }

    type solver_ = Solver of solver * bool ref

    let maxCS = Global.maxCSid

    let csArray =
      (Array.array (maxCS + 1, Solver (emptySolver, ref false))
        : solver_ Array.array)

    let _ = Array.update (csArray, 0, Solver (unifySolver, ref true))
    let nextCS = (ref 1 : int ref)
    let installFN = (ref (function _ -> -1) : (sigEntry -> IntSyn.cid) ref)
    let rec setInstallFN f = installFN := f

    let rec installSolver solver =
      let cs = !nextCS in
      let _ =
        begin if !nextCS > maxCS then
          raise (Error "too many constraint solvers")
        else ()
        end
      in
      let _ = Array.update (csArray, cs, Solver (solver, ref false)) in
      let _ = nextCS := !nextCS + 1 in
      cs

    let _ = installSolver unifySolver
    let activeKeywords = (ref [] : string list ref)

    let rec resetSolvers () =
      begin
        ArraySlice.appi
          (function
            | cs, Solver (solver, active) -> begin
                if !active then begin
                  active := false;
                  (fun r -> r.reset) solver ()
                end
                else ()
              end)
          (ArraySlice.slice (csArray, 0, Some !nextCS));
        begin
          activeKeywords := [];
          useSolver "Unify"
        end
      end

    and useSolver name =
      let exception Found of IntSyn.csid in
      let rec findSolver name =
        try
          begin
            ArraySlice.appi
              (function
                | cs, Solver (solver, _) -> begin
                    if (fun r -> r.name) solver = name then raise (Found cs)
                    else ()
                  end)
              (ArraySlice.slice (csArray, 0, Some !nextCS));
            None
          end
        with Found cs -> Some cs
      in
      begin match findSolver name with
      | Some cs ->
          let (Solver (solver, active)) = Array.sub (csArray, cs) in
          begin if !active then ()
          else begin
            if
              List.exists
                (function s -> s = (fun r -> r.keywords) solver)
                !activeKeywords
            then
              raise
                (Error
                   (("solver " ^ name)
                  ^ " is incompatible with a currently active solver"))
            else begin
              active := true;
              begin
                activeKeywords :=
                  (fun r -> r.keywords) solver :: !activeKeywords;
                begin
                  List.app useSolver ((fun r -> r.needs) solver);
                  (fun r -> r.init) solver (cs, !installFN)
                end
              end
            end
          end
          end
      | None -> raise (Error (("solver " ^ name) ^ " not found"))
      end

    let rec parse string =
      let exception Parsed of IntSyn.csid * IntSyn.conDec in
      let rec parse' (cs, (solver : solver)) =
        begin match (fun r -> r.fgnConst) solver with
        | None -> ()
        | Some fgnConDec -> begin
            match (fun r -> r.parse) fgnConDec string with
            | None -> ()
            | Some conDec -> raise (Parsed (cs, conDec))
          end
        end
      in
      try
        begin
          ArraySlice.appi
            (function
              | cs, Solver (solver, active) -> begin
                  if !active then parse' (cs, solver) else ()
                end)
            (ArraySlice.slice (csArray, 0, Some !nextCS));
          None
        end
      with Parsed (csid, conDec) -> Some (csid, conDec)

    let markCount = (ref 0 : int ref)

    let rec reset () =
      ArraySlice.appi
        (function
          | _, Solver (solver, active) -> begin
              if !active then begin
                markCount := 0;
                (fun r -> r.reset) solver ()
              end
              else ()
            end)
        (ArraySlice.slice (csArray, 0, Some !nextCS))

    let rec mark () =
      begin
        markCount := !markCount + 1;
        ArraySlice.appi
          (function
            | _, Solver (solver, active) -> begin
                if !active then (fun r -> r.mark) solver () else ()
              end)
          (ArraySlice.slice (csArray, 0, Some !nextCS))
      end

    let rec unwind targetCount =
      let rec unwind' = function
        | 0 -> markCount := targetCount
        | k -> begin
            ArraySlice.appi
              (function
                | _, Solver (solver, active) -> begin
                    if !active then (fun r -> r.unwind) solver () else ()
                  end)
              (ArraySlice.slice (csArray, 0, Some !nextCS));
            unwind' (k - 1)
          end
      in
      unwind' (!markCount - targetCount)

    let rec trail f =
      let current = !markCount in
      let _ = mark () in
      let r = f () in
      let _ = unwind current in
      r
  end

  (* vacuous solver *)
  (* Stelf unification as a constraint solver *)
  (* List of installed solvers *)
  (* Installing function *)
  (* install the specified solver *)
  (* val _ = print (""Installing constraint domain "" ^ #name solver ^ ""\n"") *)
  (* install the unification solver *)
  (* make all the solvers inactive *)
  (* make the specified solver active *)
  (* ask each active solver to try and parse the given string *)
  (* reset the internal status of all the active solvers *)
  (* mark all active solvers *)
  (* unwind all active solvers *)
  (* trail the give function *)
  let setInstallFN = setInstallFN
  let installSolver = installSolver
  let resetSolvers = resetSolvers
  let useSolver = useSolver
  let parse = parse
  let reset = reset
  let trail = trail
end

(*! structure ModeSyn : MODESYN !*)
(* functor CsManager *)
include MakeCsManager (struct
  module Global = Global

  (*! structure IntSyn = IntSyn !*)
  module Unify = UnifyTrail
  module Fixity = Names.Fixity
end)

(* # 1 "src/solvers/CsManager.sml.ml" *)
