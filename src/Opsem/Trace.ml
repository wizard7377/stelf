open! Intsyn.Lambda_
open! Names.Names_
open! Print.Print_

(* # 1 "src/opsem/Trace.sig.ml" *)
include TRACE

(* reset trace, break, detail *)
(* signature TRACE *)

(* # 1 "src/opsem/Trace.fun.ml" *)
open! Basis

module Trace (Trace__0 : sig
  (*! structure IntSyn' : INTSYN !*)
  module Names : NAMES

  (*! sharing Names.IntSyn = IntSyn' !*)
  module Whnf : WHNF

  (*! sharing Whnf.IntSyn = IntSyn' !*)
  module Abstract : ABSTRACT

  (*! sharing Abstract.IntSyn = IntSyn' !*)
  module Print : PRINT
end) : TRACE = struct
  open Trace__0

  (*! structure IntSyn = IntSyn' !*)
  open! struct
    module I = IntSyn
    module P = Print
    module N = Names
  end

  (* Printing Utilities *)
  let headToString (g, a) = match a with
    | I.Const c -> N.qidToString (N.constQid c)
    | I.Def d -> N.qidToString (N.constQid d)
    | I.BVar k -> N.bvarName g k

  let expToString g u = P.expToString g u ^ ". "
  let decToString g d = P.decToString g d ^ ". "

  let eqnToString (g, u1, u2) =
    ((P.expToString g u1 ^ " = ") ^ P.expToString g u2) ^ ". "

  let newline () = print "\n"

  let rec printCtx = function
    | I.Null -> print "No hypotheses or parameters. "
    | I.Decl (I.Null, d) -> print (decToString I.Null d)
    | I.Decl (g, d) -> begin
        printCtx g;
        begin
          newline ();
          print (decToString g d)
        end
      end

  let evarsToString xnames =
    let inst = P.evarInstToString xnames in
    let constrOpt = P.evarCnstrsToStringOpt xnames in
    begin match constrOpt with
    | None -> inst
    | Some constr -> (inst ^ "\nConstraints:\n") ^ constr
    end

  let rec varsToEVarInst = function
    | [] -> []
    | name :: names ->
        begin match N.getEVarOpt name with
        | None -> begin
            print (("Trace warning: ignoring unknown variable " ^ name) ^ "\n");
            varsToEVarInst names
          end
        | Some x -> (x, name) :: varsToEVarInst names
        end

  let printVars names = print (evarsToString (varsToEVarInst names))

  let printVarstring line =
    printVars (List.tl (String.tokens Char.isSpace line))

  type 'a spec = None | Some of 'a list | All

  let traceSpec : string spec ref = ref None
  let breakSpec : string spec ref = ref None

  let trace = function
    | None -> traceSpec := None
    | Some names -> traceSpec := Some names
    | All -> traceSpec := All

  let break = function
    | None -> breakSpec := None
    | Some names -> breakSpec := Some names
    | All -> breakSpec := All

  let detail = ref 1

  let setDetail : int option -> unit = function
    | None -> print "Trace warning: detail is not a valid integer\n"
    | Some n ->
        begin if 0 <= n then detail := n
        else print "Trace warning: detail must be positive\n"
        end
  (* andalso n <= 2 *)

  let traceTSpec : I.cid spec ref = ref None
  let breakTSpec : I.cid spec ref = ref None

  let rec toCids = function
    | [] -> []
    | name :: names ->
        begin match N.stringToQid name with
        | None -> begin
            print
              (("Trace warning: ignoring malformed qualified identifier " ^ name)
              ^ "\n");
            toCids names
          end
        | Some qid ->
            begin match N.constLookup qid with
            | None -> begin
                print
                  (("Trace warning: ignoring undeclared constant "
                  ^ N.qidToString qid)
                  ^ "\n");
                toCids names
              end
            | Some cid -> cid :: toCids names
            end
        end

  let initTrace = function
    | None -> traceTSpec := None
    | Some names -> traceTSpec := Some (toCids names)
    | All -> traceTSpec := All

  let initBreak = function
    | None -> breakTSpec := None
    | Some names -> breakTSpec := Some (toCids names)
    | All -> breakTSpec := All

  let printHelp () =
    print
      "<newline> - continue --- execute with current settings\n\
       n - next --- take a single step\n\
       r - run --- remove all breakpoints and continue\n\
       s - skip --- skip until current subgoals succeeds, is retried, or fails\n\
       s n - skip to n --- skip until goal (n) is considered\n\
       t - trace --- trace all events\n\
       u - untrace --- trace no events\n\
       d n - detail --- set trace detail to n (0, 1, or 2)\n\
       h - hypotheses --- show current hypotheses\n\
       g - goal --- show current goal\n\
       i - instantiation --- show instantiation of variables in current goal\n\
       v X1 ... Xn - variables --- show instantiation of X1 ... Xn\n\
       ? for help"

  let currentGoal : (I.dctx * I.exp) ref = ref (I.Null, I.Uni I.Type)

  (* dummy initialization *)
  let currentEVarInst : (I.exp * string) list ref = ref []

  let setEVarInst xs =
    currentEVarInst :=
      List.map (function x -> (x, N.evarName I.Null x)) xs

  let setGoal (g, v) =
    begin
      currentGoal := (g, v);
      setEVarInst (Abstract.collectEVars g (v, I.id) [])
    end

  type nonrec goalTag = int option

  let tag : goalTag ref = ref (None : goalTag)

  let tagGoal () : goalTag =
    begin match !tag with
    | None -> None
    | Some n -> begin
        tag := Some (n + 1);
        !tag
      end
    end

  let watchForTag : goalTag ref = ref (None : goalTag)

  let initTag () =
    begin
      watchForTag := None;
      begin match (!traceTSpec, !breakTSpec) with
      | None, None -> tag := None
      | _ -> tag := Some 0
      end
    end

  let setWatchForTag : goalTag -> unit = function
    | None -> watchForTag := !tag
    | Some n -> watchForTag := Some n

  let rec breakAction g =
    ignore (print " ");
    let line = input_line stdin in
    begin match String.sub (line, 0) with
    | '\n' -> ()
    | 'n' -> breakTSpec := All
    | 'r' -> breakTSpec := None
    | 's' -> setWatchForTag (Int.fromString (String.extract (line, 1, None)))
    | 't' -> begin
        traceTSpec := All;
        begin
          print "% Now tracing all";
          breakAction g
        end
      end
    | 'u' -> begin
        traceTSpec := None;
        begin
          print "% Now tracing none";
          breakAction g
        end
      end
    | 'd' -> begin
        setDetail (Int.fromString (String.extract (line, 1, None)));
        begin
          print ("% Trace detail now " ^ Int.toString !detail);
          breakAction g
        end
      end
    | 'h' -> begin
        printCtx g;
        breakAction g
      end
    | 'g' -> begin
        print (let g__, u__ = !currentGoal in expToString g__ u__);
        breakAction g
      end
    | 'i' -> begin
        print (evarsToString (List.rev !currentEVarInst));
        breakAction g
      end
    | 'v' -> begin
        printVarstring line;
        breakAction g
      end
    | '?' -> begin
        printHelp ();
        breakAction g
      end
    | _ -> begin
        print "unrecognized command (? for help)";
        breakAction g
      end
    end

  let init () =
    begin
      initTrace !traceSpec;
      begin
        initBreak !breakSpec;
        initTag ()
      end
    end

  type event =
    | IntroHyp of IntSyn.head * IntSyn.dec
    | DischargeHyp of IntSyn.head * IntSyn.dec
    | IntroParm of IntSyn.head * IntSyn.dec
    | DischargeParm of IntSyn.head * IntSyn.dec
    | Resolved of IntSyn.head * IntSyn.head
    | Subgoal of (IntSyn.head * IntSyn.head) * (unit -> int)
    | SolveGoal of goalTag * IntSyn.head * IntSyn.exp
    | SucceedGoal of goalTag * (IntSyn.head * IntSyn.head) * IntSyn.exp
    | CommitGoal of goalTag * (IntSyn.head * IntSyn.head) * IntSyn.exp
    | RetryGoal of goalTag * (IntSyn.head * IntSyn.head) * IntSyn.exp
    | FailGoal of goalTag * IntSyn.head * IntSyn.exp
    | Unify of (IntSyn.head * IntSyn.head) * IntSyn.exp * IntSyn.exp
    | FailUnify of (IntSyn.head * IntSyn.head) * string

  (* resolved with clause c, fam a *)
  (* clause c, fam a, nth subgoal *)
  (* clause c failed, fam a *)
  (* clause head == goal *)
  (* failure message *)
  let eventToString (g, a) = match a with
    | IntroHyp (_, d) -> "% Introducing hypothesis\n" ^ decToString g d
    | DischargeHyp (_, I.Dec (Some x, _)) -> "% Discharging hypothesis " ^ x
    | IntroParm (_, d) -> "% Introducing parameter\n" ^ decToString g d
    | DischargeParm (_, I.Dec (Some x, _)) -> "% Discharging parameter " ^ x
    | Resolved (hc, ha) ->
        (("% Resolved with clause " ^ headToString (g, hc)) ^ "\n")
        ^ evarsToString (List.rev !currentEVarInst)
    | Subgoal ((hc, ha), msg) ->
        (("% Solving subgoal (" ^ Int.toString (msg ())) ^ ") of clause ")
        ^ headToString (g, hc)
    | SolveGoal (Some tag, _, v) ->
        (("% Goal " ^ Int.toString tag) ^ ":\n") ^ expToString g v
    | SucceedGoal (Some tag, _, v) ->
        ("% Goal " ^ Int.toString tag) ^ " succeeded"
    | CommitGoal (Some tag, _, v) ->
        ("% Goal " ^ Int.toString tag) ^ " committed to first solution"
    | RetryGoal (Some tag, (hc, ha), v) ->
        ((((("% Backtracking from clause " ^ headToString (g, hc)) ^ "\n")
          ^ "% Retrying goal ")
         ^ Int.toString tag)
        ^ ":\n")
        ^ expToString g v
    | FailGoal (Some tag, _, v) -> "% Failed goal " ^ Int.toString tag
    | Unify ((hc, ha), q, p) ->
        (("% Trying clause " ^ headToString (g, hc)) ^ "\n")
        ^ eqnToString (g, q, p)
    | FailUnify ((hc, ha), msg) ->
        (("% Unification failed with clause " ^ headToString (g, hc)) ^ ":\n")
        ^ msg

  let traceEvent (g, e) = print (eventToString (g, e))

  let monitorHead (cids, a) = match a with
    | I.Const c -> List.exists (function c' -> c = c') cids
    | I.Def d -> List.exists (function c' -> d = c') cids
    | I.BVar k -> false

  let monitorHeads (cids, (hc, ha)) =
    monitorHead (cids, hc) || monitorHead (cids, ha)

  let monitorEvent (cids, a) = match a with
    | IntroHyp (h, _) -> monitorHead (cids, h)
    | DischargeHyp (h, _) -> monitorHead (cids, h)
    | IntroParm (h, _) -> monitorHead (cids, h)
    | DischargeParm (h, _) -> monitorHead (cids, h)
    | SolveGoal (_, h, v) -> monitorHead (cids, h)
    | SucceedGoal (_, (hc, ha), _) -> monitorHeads (cids, (hc, ha))
    | CommitGoal (_, (hc, ha), _) -> monitorHeads (cids, (hc, ha))
    | RetryGoal (_, (hc, ha), _) -> monitorHeads (cids, (hc, ha))
    | FailGoal (_, h, _) -> monitorHead (cids, h)
    | Resolved (hc, ha) -> monitorHeads (cids, (hc, ha))
    | Subgoal ((hc, ha), _) -> monitorHeads (cids, (hc, ha))
    | Unify ((hc, ha), _, _) -> monitorHeads (cids, (hc, ha))
    | FailUnify ((hc, ha), _) -> monitorHeads (cids, (hc, ha))

  let monitorDetail = function
    | Unify _ -> !detail >= 2
    | FailUnify _ -> !detail >= 2
    | _ -> !detail >= 1

  (* expensive if tracing Unify! *)
  (* but: maintain only if break or trace is on *)
  (* may not be sufficient for some information *)
  let maintain = function
    | g, SolveGoal (_, _, v) -> setGoal (g, v)
    | g, RetryGoal (_, _, v) -> setGoal (g, v)
    | g, FailGoal (_, _, v) -> setGoal (g, v)
    | g, Unify (_, q, p) ->
        setEVarInst
          (Abstract.collectEVars
             g (p, I.id) (Abstract.collectEVars g (q, I.id) []))
    | _ -> ()
  (* show substitution for variables in clause head if tracing unification *)

  let monitorBreak (a, g, e) = match a with
    | None -> false
    | Some cids ->
        begin if monitorEvent (cids, e) then begin
          maintain (g, e);
          begin
            traceEvent (g, e);
            begin
              breakAction g;
              true
            end
          end
        end
        else false
        end
    | All -> begin
        maintain (g, e);
        begin
          traceEvent (g, e);
          begin
            breakAction g;
            true
          end
        end
      end

  let monitorTrace (a, g, e) = match a with
    | None -> false
    | Some cids ->
        begin if monitorEvent (cids, e) then begin
          maintain (g, e);
          begin
            traceEvent (g, e);
            begin
              newline ();
              true
            end
          end
        end
        else false
        end
    | All -> begin
        maintain (g, e);
        begin
          traceEvent (g, e);
          begin
            newline ();
            true
          end
        end
      end

  let watchFor e =
    begin match !watchForTag with
    | None -> false
    | Some t ->
        begin match e with
        | SolveGoal (Some t', _, _) -> t' = t
        | SucceedGoal (Some t', _, _) -> t' = t
        | CommitGoal (Some t', _, _) -> t' = t
        | RetryGoal (Some t', _, _) -> t' = t
        | FailGoal (Some t', _, _) -> t' = t
        | _ -> false
        end
    end

  let skipping () =
    begin match !watchForTag with None -> false | Some _ -> true
    end

  let rec signal g e =
    begin if monitorDetail e then
      begin if skipping () then
        begin if watchFor e then begin
          watchForTag := None;
          signal g e
        end
        else begin
          ignore (monitorTrace (!traceTSpec, g, e));
          ()
        end
        end
      else
        begin if monitorBreak (!breakTSpec, g, e) then ()
        else begin
          ignore (monitorTrace (!traceTSpec, g, e));
          ()
        end
        end (* stops, continues after input *)
      end
    else ()
    end
  (* prints trace, continues *)

  let showSpec (msg, a) = match a with
    | None -> print (msg ^ " = None\n")
    | Some names -> begin
        print (msg ^ " = Some [");
        begin
          List.app (function name -> print (" " ^ name)) names;
          print "]\n"
        end
      end
    | All -> print (msg ^ " = All\n")

  let tracing () =
    begin match (!traceSpec, !breakSpec) with None, None -> false | _ -> true
    end

  let show () =
    begin
      showSpec ("trace", !traceSpec);
      begin
        showSpec ("break", !breakSpec);
        print (("detail = " ^ Int.toString !detail) ^ "\n")
      end
    end

  let reset () =
    begin
      trace None;
      begin
        break None;
        detail := 1
      end
    end
end
(*! sharing Print.IntSyn = IntSyn' !*)
(* functor Trace *)

(* # 1 "src/opsem/Trace.sml.ml" *)
