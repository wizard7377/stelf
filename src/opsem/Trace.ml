(* # 1 "src/opsem/Trace.sig.ml" *)
open! Basis
include Trace_intf
(* reset trace, break, detail *)
(* signature TRACE *)

(* # 1 "src/opsem/Trace.fun.ml" *)
open! Abstract
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
  let rec headToString = function
    | g_, I.Const c -> N.qidToString (N.constQid c)
    | g_, I.Def d -> N.qidToString (N.constQid d)
    | g_, I.BVar k -> N.bvarName (g_, k)

  let rec expToString gu_ = P.expToString gu_ ^ ". "
  let rec decToString gd_ = P.decToString gd_ ^ ". "

  let rec eqnToString (g_, u1_, u2_) =
    ((P.expToString (g_, u1_) ^ " = ") ^ P.expToString (g_, u2_)) ^ ". "

  let rec newline () = print "\n"

  let rec printCtx = function
    | I.Null -> print "No hypotheses or parameters. "
    | I.Decl (I.Null, d_) -> print (decToString (I.Null, d_))
    | I.Decl (g_, d_) -> begin
        printCtx g_;
        begin
          newline ();
          print (decToString (g_, d_))
        end
      end

  let rec evarsToString xnames_ =
    let inst = P.evarInstToString xnames_ in
    let constrOpt = P.evarCnstrsToStringOpt xnames_ in
    begin match constrOpt with
    | None -> inst
    | Some constr -> (inst ^ "\nConstraints:\n") ^ constr
    end

  let rec varsToEVarInst = function
    | [] -> []
    | name :: names -> begin
        match N.getEVarOpt name with
        | None -> begin
            print (("Trace warning: ignoring unknown variable " ^ name) ^ "\n");
            varsToEVarInst names
          end
        | Some x_ -> (x_, name) :: varsToEVarInst names
      end

  let rec printVars names = print (evarsToString (varsToEVarInst names))

  let rec printVarstring line =
    printVars (List.tl (String.tokens Char.isSpace line))

  type 'a spec = None | Some of 'a list | All

  let traceSpec : string spec ref = ref None
  let breakSpec : string spec ref = ref None

  let rec trace = function
    | None -> traceSpec := None
    | Some names -> traceSpec := Some names
    | All -> traceSpec := All

  let rec break = function
    | None -> breakSpec := None
    | Some names -> breakSpec := Some names
    | All -> breakSpec := All

  let detail = ref 1

  let rec setDetail : int option -> unit = function
    | None -> print "Trace warning: detail is not a valid integer\n"
    | Some n -> begin
        if 0 <= n then detail := n
        else print "Trace warning: detail must be positive\n"
      end
  (* andalso n <= 2 *)

  let traceTSpec : I.cid spec ref = ref None
  let breakTSpec : I.cid spec ref = ref None

  let rec toCids = function
    | [] -> []
    | name :: names -> begin
        match N.stringToQid name with
        | None -> begin
            print
              (("Trace warning: ignoring malformed qualified identifier " ^ name)
              ^ "\n");
            toCids names
          end
        | Some qid -> begin
            match N.constLookup qid with
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

  let rec initTrace = function
    | None -> traceTSpec := None
    | Some names -> traceTSpec := Some (toCids names)
    | All -> traceTSpec := All

  let rec initBreak = function
    | None -> breakTSpec := None
    | Some names -> breakTSpec := Some (toCids names)
    | All -> breakTSpec := All

  let rec printHelp () =
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

  let rec setEVarInst xs_ =
    currentEVarInst :=
      List.map (function x_ -> (x_, N.evarName (I.Null, x_))) xs_

  let rec setGoal (g_, v_) =
    begin
      currentGoal := (g_, v_);
      setEVarInst (Abstract.collectEVars (g_, (v_, I.id), []))
    end

  type nonrec goalTag = int option

  let tag : goalTag ref = ref (None : goalTag)

  let rec tagGoal () : goalTag =
    begin match !tag with
    | None -> None
    | Some n -> begin
        tag := Some (n + 1);
        !tag
      end
    end

  let watchForTag : goalTag ref = ref (None : goalTag)

  let rec initTag () =
    begin
      watchForTag := None;
      begin match (!traceTSpec, !breakTSpec) with
      | None, None -> tag := None
      | _ -> tag := Some 0
      end
    end

  let rec setWatchForTag : goalTag -> unit = function
    | None -> watchForTag := !tag
    | Some n -> watchForTag := Some n

  let rec breakAction g_ =
    let _ = print " " in
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
          breakAction g_
        end
      end
    | 'u' -> begin
        traceTSpec := None;
        begin
          print "% Now tracing none";
          breakAction g_
        end
      end
    | 'd' -> begin
        setDetail (Int.fromString (String.extract (line, 1, None)));
        begin
          print ("% Trace detail now " ^ Int.toString !detail);
          breakAction g_
        end
      end
    | 'h' -> begin
        printCtx g_;
        breakAction g_
      end
    | 'g' -> begin
        print (expToString !currentGoal);
        breakAction g_
      end
    | 'i' -> begin
        print (evarsToString (List.rev !currentEVarInst));
        breakAction g_
      end
    | 'v' -> begin
        printVarstring line;
        breakAction g_
      end
    | '?' -> begin
        printHelp ();
        breakAction g_
      end
    | _ -> begin
        print "unrecognized command (? for help)";
        breakAction g_
      end
    end

  let rec init () =
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
  let rec eventToString = function
    | g_, IntroHyp (_, d_) -> "% Introducing hypothesis\n" ^ decToString (g_, d_)
    | g_, DischargeHyp (_, I.Dec (Some x, _)) -> "% Discharging hypothesis " ^ x
    | g_, IntroParm (_, d_) -> "% Introducing parameter\n" ^ decToString (g_, d_)
    | g_, DischargeParm (_, I.Dec (Some x, _)) -> "% Discharging parameter " ^ x
    | g_, Resolved (hc_, ha_) ->
        (("% Resolved with clause " ^ headToString (g_, hc_)) ^ "\n")
        ^ evarsToString (List.rev !currentEVarInst)
    | g_, Subgoal ((hc_, ha_), msg) ->
        (("% Solving subgoal (" ^ Int.toString (msg ())) ^ ") of clause ")
        ^ headToString (g_, hc_)
    | g_, SolveGoal (Some tag, _, v_) ->
        (("% Goal " ^ Int.toString tag) ^ ":\n") ^ expToString (g_, v_)
    | g_, SucceedGoal (Some tag, _, v_) ->
        ("% Goal " ^ Int.toString tag) ^ " succeeded"
    | g_, CommitGoal (Some tag, _, v_) ->
        ("% Goal " ^ Int.toString tag) ^ " committed to first solution"
    | g_, RetryGoal (Some tag, (hc_, ha_), v_) ->
        ((((("% Backtracking from clause " ^ headToString (g_, hc_)) ^ "\n")
          ^ "% Retrying goal ")
         ^ Int.toString tag)
        ^ ":\n")
        ^ expToString (g_, v_)
    | g_, FailGoal (Some tag, _, v_) -> "% Failed goal " ^ Int.toString tag
    | g_, Unify ((hc_, ha_), q_, p_) ->
        (("% Trying clause " ^ headToString (g_, hc_)) ^ "\n")
        ^ eqnToString (g_, q_, p_)
    | g_, FailUnify ((hc_, ha_), msg) ->
        (("% Unification failed with clause " ^ headToString (g_, hc_)) ^ ":\n")
        ^ msg

  let rec traceEvent (g_, e) = print (eventToString (g_, e))

  let rec monitorHead = function
    | cids, I.Const c -> List.exists (function c' -> c = c') cids
    | cids, I.Def d -> List.exists (function c' -> d = c') cids
    | cids, I.BVar k -> false

  let rec monitorHeads (cids, (hc_, ha_)) =
    monitorHead (cids, hc_) || monitorHead (cids, ha_)

  let rec monitorEvent = function
    | cids, IntroHyp (h_, _) -> monitorHead (cids, h_)
    | cids, DischargeHyp (h_, _) -> monitorHead (cids, h_)
    | cids, IntroParm (h_, _) -> monitorHead (cids, h_)
    | cids, DischargeParm (h_, _) -> monitorHead (cids, h_)
    | cids, SolveGoal (_, h_, v_) -> monitorHead (cids, h_)
    | cids, SucceedGoal (_, (hc_, ha_), _) -> monitorHeads (cids, (hc_, ha_))
    | cids, CommitGoal (_, (hc_, ha_), _) -> monitorHeads (cids, (hc_, ha_))
    | cids, RetryGoal (_, (hc_, ha_), _) -> monitorHeads (cids, (hc_, ha_))
    | cids, FailGoal (_, h_, _) -> monitorHead (cids, h_)
    | cids, Resolved (hc_, ha_) -> monitorHeads (cids, (hc_, ha_))
    | cids, Subgoal ((hc_, ha_), _) -> monitorHeads (cids, (hc_, ha_))
    | cids, Unify ((hc_, ha_), _, _) -> monitorHeads (cids, (hc_, ha_))
    | cids, FailUnify ((hc_, ha_), _) -> monitorHeads (cids, (hc_, ha_))

  let rec monitorDetail = function
    | Unify _ -> !detail >= 2
    | FailUnify _ -> !detail >= 2
    | _ -> !detail >= 1

  (* expensive if tracing Unify! *)
  (* but: maintain only if break or trace is on *)
  (* may not be sufficient for some information *)
  let rec maintain = function
    | g_, SolveGoal (_, _, v_) -> setGoal (g_, v_)
    | g_, RetryGoal (_, _, v_) -> setGoal (g_, v_)
    | g_, FailGoal (_, _, v_) -> setGoal (g_, v_)
    | g_, Unify (_, q_, p_) ->
        setEVarInst
          (Abstract.collectEVars
             (g_, (p_, I.id), Abstract.collectEVars (g_, (q_, I.id), [])))
    | _ -> ()
  (* show substitution for variables in clause head if tracing unification *)

  let rec monitorBreak = function
    | None, g_, e -> false
    | Some cids, g_, e -> begin
        if monitorEvent (cids, e) then begin
          maintain (g_, e);
          begin
            traceEvent (g_, e);
            begin
              breakAction g_;
              true
            end
          end
        end
        else false
      end
    | All, g_, e -> begin
        maintain (g_, e);
        begin
          traceEvent (g_, e);
          begin
            breakAction g_;
            true
          end
        end
      end

  let rec monitorTrace = function
    | None, g_, e -> false
    | Some cids, g_, e -> begin
        if monitorEvent (cids, e) then begin
          maintain (g_, e);
          begin
            traceEvent (g_, e);
            begin
              newline ();
              true
            end
          end
        end
        else false
      end
    | All, g_, e -> begin
        maintain (g_, e);
        begin
          traceEvent (g_, e);
          begin
            newline ();
            true
          end
        end
      end

  let rec watchFor e =
    begin match !watchForTag with
    | None -> false
    | Some t -> begin
        match e with
        | SolveGoal (Some t', _, _) -> t' = t
        | SucceedGoal (Some t', _, _) -> t' = t
        | CommitGoal (Some t', _, _) -> t' = t
        | RetryGoal (Some t', _, _) -> t' = t
        | FailGoal (Some t', _, _) -> t' = t
        | _ -> false
      end
    end

  let rec skipping () =
    begin match !watchForTag with None -> false | Some _ -> true
    end

  let rec signal (g_, e) =
    begin if monitorDetail e then begin
      if skipping () then begin
        if watchFor e then begin
          watchForTag := None;
          signal (g_, e)
        end
        else begin
          ignore (monitorTrace (!traceTSpec, g_, e));
          ()
        end
      end
      else begin
        if monitorBreak (!breakTSpec, g_, e) then ()
        else begin
          ignore (monitorTrace (!traceTSpec, g_, e));
          ()
        end
      end (* stops, continues after input *)
    end
    else ()
    end
  (* prints trace, continues *)

  let rec showSpec = function
    | msg, None -> print (msg ^ " = None\n")
    | msg, Some names -> begin
        print (msg ^ " = Some [");
        begin
          List.app (function name -> print (" " ^ name)) names;
          print "]\n"
        end
      end
    | msg, All -> print (msg ^ " = All\n")

  let rec tracing () =
    begin match (!traceSpec, !breakSpec) with None, None -> false | _ -> true
    end

  let rec show () =
    begin
      showSpec ("trace", !traceSpec);
      begin
        showSpec ("break", !breakSpec);
        print (("detail = " ^ Int.toString !detail) ^ "\n")
      end
    end

  let rec reset () =
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
