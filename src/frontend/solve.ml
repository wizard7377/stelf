(* # 1 "src/frontend/solve.sig.ml" *)
open! Basis

(* Solve and query declarations, interactive top level *)
(* Author: Frank Pfenning *)
module type SOLVE = sig
  (*! structure IntSyn : INTSYN !*)
  (*! structure Paths : PATHS !*)
  module ExtQuery : Recon_query.EXTQUERY

  exception AbortQuery of string

  val solve :
    ExtQuery.define list * ExtQuery.solve * Paths.location ->
    (IntSyn.conDec_ * Paths.occConDec option) list

  val query :
    (int option * int option * ExtQuery.query) * Paths.location -> unit

  (* may raise AbortQuery(msg) *)
  val querytabled :
    (int option * int option * ExtQuery.query) * Paths.location -> unit

  (* may raise AbortQuery(msg) *)
  val qLoop : unit -> bool

  (* true means normal exit *)
  val qLoopT : unit -> bool
end

(* true means normal exit *)
(* signature SOLVE *)

(* # 1 "src/frontend/solve.fun.ml" *)
open! Parser
open! Basis

(* Front End Interface *)
(* Author: Frank Pfenning *)
(* Modified: Carsten Schuermann, Jeff Polakow, Roberto Virga *)
module Solve (Solve__0 : sig
  module Global : GLOBAL

  (*! structure IntSyn' : INTSYN !*)
  module Names : NAMES

  (*! sharing Names.IntSyn = IntSyn' !*)
  module ReconQuery : Recon_query.RECON_QUERY

  module Parser :
    PARSER
      with type ExtQuery.query = ReconQuery.query
       and type ExtQuery.define = ReconQuery.define
       and type ExtQuery.solve = ReconQuery.solve

  (*! sharing ReconQuery.IntSyn = IntSyn' !*)
  (* sharing type ReconQuery.Paths.occConDec = Origins.Paths.occConDec *)
  module Timers : Timers.TIMERS

  (*! structure CompSyn : COMPSYN !*)
  (*! sharing CompSyn.IntSyn = IntSyn' !*)
  module Compile : COMPILE

  (*! sharing Compile.IntSyn = IntSyn' !*)
  (*! sharing Compile.CompSyn = CompSyn !*)
  module CPrint : CPRINT

  (*! sharing CPrint.IntSyn = IntSyn' !*)
  (*! sharing CPrint.CompSyn = CompSyn !*)
  (*! structure Cs_manager : CS_MANAGER !*)
  (*! sharing Cs_manager.IntSyn = IntSyn' !*)
  module AbsMachine : Absmachine.ABSMACHINE

  (*! sharing AbsMachine.IntSyn = IntSyn' !*)
  (*! sharing AbsMachine.CompSyn = CompSyn !*)
  module AbsMachineSbt : Absmachine_sbt.ABSMACHINESBT

  (*! sharing AbsMachineSbt.IntSyn = IntSyn' !*)
  (*! sharing AbsMachineSbt.CompSyn = CompSyn!*)
  module PtRecon : Ptrecon.PTRECON

  (*! sharing PtRecon.IntSyn = IntSyn' !*)
  (*! sharing PtRecon.CompSyn = CompSyn !*)
  (*! structure TableParam : TABLEPARAM !*)
  module Tabled : Tabled_machine.TABLED

  (*! sharing Tabled.IntSyn = IntSyn' !*)
  (*! sharing Tabled.CompSyn = CompSyn !*)
  (*! structure MemoTable : MEMOTABLE !*)
  (*! sharing MemoTable.IntSyn = IntSyn' !*)
  module Print : PRINT

  (*! sharing Print.IntSyn = IntSyn' !*)
  module Msg : MSG
end) : SOLVE with module ExtQuery = Solve__0.ReconQuery = struct
  (*! structure IntSyn = IntSyn' !*)
  module Global = Solve__0.Global
  module Names = Solve__0.Names
  module Parser = Solve__0.Parser
  module ReconQuery = Solve__0.ReconQuery
  module Timers = Solve__0.Timers
  module TimeLimit = Time_limit.TimeLimit
  module Compile = Solve__0.Compile
  module CompSyn = CompSyn.CompSyn
  module CPrint = Solve__0.CPrint
  module AbsMachine = Solve__0.AbsMachine
  module AbsMachineSbt = Solve__0.AbsMachineSbt
  module PtRecon = Solve__0.PtRecon
  module Tabled = Solve__0.Tabled
  module TableParam = Table_param.TableParam
  module Print = Solve__0.Print
  module Msg = Solve__0.Msg
  module ExtQuery = ReconQuery

  (*! structure Paths = ReconQuery.Paths !*)
  module S = Parser.Stream

  let rec inputLine97 instream =
    begin match TextIO.inputLine instream with Some s -> s | None -> ""
    end

  (* evarInstToString Xs = msg
     formats instantiated EVars as a substitution.
     Abbreviate as empty string if chatter level is < 3.
  *)
  let rec evarInstToString xs_ =
    begin if !Global.chatter >= 3 then Print.evarInstToString xs_ else ""
    end

  (* expToString (G, U) = msg
     formats expression as a string.
     Abbreviate as empty string if chatter level is < 3.
  *)
  let rec expToString gu_ =
    begin if !Global.chatter >= 3 then Print.expToString gu_ else ""
    end

  (* exception AbortQuery
     is raised when a %query declaration has an unexpected number of solutions
     or of %solve has no solution.
  *)
  exception AbortQuery of string

  (* Bounds SOME(n) for n >= 0, NONE represents positive infinity *)
  (* Concrete syntax: 0, 1, 2, ..., * *)
  type nonrec bound = int option

  (* exceeds : bound * bound -> bool *)
  let rec exceeds = function
    | Some n, Some m -> n >= m
    | Some n, None -> false
    | None, _ -> true

  (* boundEq : bound * bound -> bool *)
  let rec boundEq = function
    | Some n, Some m -> n = m
    | None, None -> true
    | _ -> false

  (* boundToString : bound -> string *)
  let rec boundToString = function Some n -> Int.toString n | None -> "*"

  (* boundMin : bound * bound -> bound *)
  let rec boundMin = function
    | Some n, Some m -> Some (Int.min (n, m))
    | b, None -> b
    | None, b -> b

  (* checkSolutions : bound * bound * int -> unit *)
  (* raises AbortQuery(msg) if the actual solutions do not match *)
  (* the expected number, given the bound on the number of tries *)
  let rec checkSolutions (expected, try_, solutions) =
    begin if boundEq (boundMin (expected, try_), Some solutions) then ()
    else
      raise
        (AbortQuery
           ((((("Query error -- wrong number of solutions: expected "
              ^ boundToString expected)
              ^ " in ")
             ^ boundToString try_)
            ^ " tries, but found ")
           ^ Int.toString solutions))
    end

  (* checkStages : bound * int -> unit *)
  (* raises AbortQuery(msg) if the actual #stages do not match *)
  (* the expected number, given the bound on the number of tries *)
  let rec checkStages (try_, stages) =
    begin if boundEq (try_, Some stages) then ()
    else
      raise
        (AbortQuery
           ((("Query error -- wrong number of stages: " ^ boundToString try_)
            ^ " tries, but terminated after  ")
           ^ Int.toString stages))
    end

  (* moreSolutions () = b  iff  the user requests more solutions
     Effects: inputs one line from standard input,
              raises exception AbortQuery(msg) is first character is ""q"" or ""Q""
  *)
  let rec moreSolutions () =
    begin
      print "More? ";
      begin match String.sub (inputLine97 TextIO.stdIn, 0) with
      | 'y' -> true
      | 'Y' -> true
      | ';' -> true
      | 'q' -> raise (AbortQuery "Query error -- explicit quit")
      | 'Q' -> raise (AbortQuery "Query error -- explicit quit")
      | _ -> false
      end
    end

  (* exception Done is raised by the initial success continuation
     when no further solutions are requested.
  *)
  exception Done

  (* exception Completed raised by tabled computation when table is saturated *)
  exception Completed

  (* exception Solution (imp, (M, A))
     is raised when M : A is the generalized form of a solution to the
     query A', where imp is the number of implicitly quantified arguments.
  *)
  exception Solution of IntSyn.exp_
  exception SolutionSkel of CompSyn.pskeleton

  (* readfile (fileName) = status
     reads and processes declarations from fileName in order, issuing
     error messages and finally returning the status (either OK or
     ABORT).
  *)
  let rec solve' (defines, solve_, Paths.Loc (fileName, r)) =
    let a_, finish =
      ReconQuery.solveToSolve (defines, solve_, Paths.Loc (fileName, r))
    in
    let _ =
      begin if !Global.chatter >= 3 then Msg.message "%solve " else ()
      end
    in
    let _ =
      begin if !Global.chatter >= 3 then
        Msg.message
          (("\n" ^ Timers.time Timers.printing expToString (IntSyn.null_, a_))
          ^ ".\n")
      else ()
      end
    in
    let g =
      Timers.time Timers.compiling Compile.compileGoal (IntSyn.null_, a_)
    in
    let rec search () =
      AbsMachine.solve
        ( (g, IntSyn.id),
          CompSyn.DProg (IntSyn.null_, IntSyn.null_),
          function m_ -> raise (Solution m_) )
    in
    begin
      Cs_manager.reset ();
      try
        begin
          TimeLimit.timeLimit !Global.timeLimit
            (Timers.time Timers.solving search)
            ();
          raise (AbortQuery "No solution to %solve found")
        end
        (* Call to solve raises Solution _ if there is a solution,
          returns () if there is none.  It could also not terminate
          *)
      with Solution m_ -> (
        try
          begin
            begin if !Global.chatter >= 3 then Msg.message " OK\n" else ()
            end;
            finish m_
          end
        with timeOut_ ->
          raise (AbortQuery "\n----------- TIME OUT ---------------\n"))
    end

  (* self timing *)
  (* echo declaration, according to chatter level *)

  (* Using substitution tree indexing for clauses in signature
   The logic programming interpreter then creates a proof skeleton
  and reconstructs the actual proof term which can be checked
  -- this version can be used to produce oracles, however no user
  directive is added yet.
*)
  let rec solveSbt (defines, solve_, Paths.Loc (fileName, r)) =
    let a_, finish =
      ReconQuery.solveToSolve (defines, solve_, Paths.Loc (fileName, r))
    in
    let _ =
      begin if !Global.chatter >= 3 then Msg.message "%solve " else ()
      end
    in
    let _ =
      begin if !Global.chatter >= 3 then
        Msg.message
          (("\n" ^ Timers.time Timers.printing expToString (IntSyn.null_, a_))
          ^ ".\n")
      else ()
      end
    in
    let g =
      Timers.time Timers.compiling Compile.compileGoal (IntSyn.null_, a_)
    in
    begin
      Cs_manager.reset ();
      try
        begin
          TimeLimit.timeLimit !Global.timeLimit
            (Timers.time Timers.solving AbsMachineSbt.solve)
            ( (g, IntSyn.id),
              CompSyn.DProg (IntSyn.null_, IntSyn.null_),
              function skel_ -> raise (SolutionSkel skel_) );
          raise (AbortQuery "No solution to %solve found")
        end
        (* Call to solve raises Solution _ if there is a solution,
          returns () if there is none.  It could also not terminate
          *)
      with SolutionSkel skel_ -> (
        try
          begin
            begin if !Global.chatter >= 2 then Msg.message " OK\n" else ()
            end;
            try
              begin
                Timers.time Timers.ptrecon PtRecon.solve
                  ( skel_,
                    (g, IntSyn.id),
                    CompSyn.DProg (IntSyn.null_, IntSyn.null_),
                    function skel_, m_ -> raise (Solution m_) );
                raise (AbortQuery "Proof reconstruction for %solve failed")
              end
            with Solution m_ -> finish m_
          end
        with timeOut_ ->
          raise (AbortQuery "\n----------- TIME OUT ---------------\n"))
    end
  (* self timing *)
  (* echo declaration, according to chatter level *)

  let rec solve args =
    begin match !Compile.optimize with
    | indexing_ -> solveSbt args
    | linearHeads_ -> solve' args
    | _ -> solve' args
    end
  (* solves A where program clauses are indexed using substitution trees
         and reconstructs the proof term X afterwards - bp
       *)

  (* %query <expected> <try> A or %query <expected> <try> X : A *)
  let rec query' ((expected, try_, quy), Paths.Loc (fileName, r)) =
    let a_, optName, xs_ =
      ReconQuery.queryToQuery (quy, Paths.Loc (fileName, r))
    in
    let _ =
      begin if !Global.chatter >= 3 then
        Msg.message
          (((("%query " ^ boundToString expected) ^ " ") ^ boundToString try_)
          ^ "\n")
      else ()
      end
    in
    let _ =
      begin if !Global.chatter >= 4 then Msg.message " " else ()
      end
    in
    let _ =
      begin if !Global.chatter >= 3 then
        Msg.message
          (("\n" ^ Timers.time Timers.printing expToString (IntSyn.null_, a_))
          ^ ".\n")
      else ()
      end
    in
    let g =
      Timers.time Timers.compiling Compile.compileGoal (IntSyn.null_, a_)
    in
    let solutions = ref 0 in
    let rec scInit m_ =
      begin
        solutions := !solutions + 1;
        begin
          begin if !Global.chatter >= 3 then begin
            Msg.message
              (("---------- Solution " ^ Int.toString !solutions)
              ^ " ----------\n");
            Msg.message (Timers.time Timers.printing evarInstToString xs_ ^ "\n")
          end
          else begin
            if !Global.chatter >= 3 then Msg.message "." else ()
          end
          end;
          begin
            begin match optName with
            | None -> ()
            | Some name -> begin
                if !Global.chatter >= 3 then
                  Msg.message
                    (Timers.time Timers.printing evarInstToString [ (m_, name) ]
                    ^ "\n")
                else ()
              end
            end;
            begin
              begin if !Global.chatter >= 3 then begin
                match
                  Timers.time Timers.printing Print.evarCnstrsToStringOpt xs_
                with
                | None -> ()
                | Some str ->
                    Msg.message (("Remaining constraints:\n" ^ str) ^ "\n")
              end
              else ()
              end
              (* Question: should we collect constraints in M? *);
              begin if exceeds (Some !solutions, try_) then raise Done else ()
              end
            end
          end
        end
      end
    in
    let rec search () =
      AbsMachine.solve
        ((g, IntSyn.id), CompSyn.DProg (IntSyn.null_, IntSyn.null_), scInit)
    in
    begin
      begin if not (boundEq (try_, Some 0)) then begin
        Cs_manager.reset ();
        begin try
          try
            TimeLimit.timeLimit !Global.timeLimit
              (Timers.time Timers.solving search)
              ()
          with Done -> ()
          (* printing is timed into solving! *)
        with timeOut_ ->
          raise (AbortQuery "\n----------- TIME OUT ---------------\n");
          begin
            Cs_manager.reset ();
            checkSolutions (expected, try_, !solutions)
          end
        end
      end
      (* solve query if bound > 0 *)
      (* in case Done was raised *)
      (* check if number of solutions is correct *)
        else begin
        if !Global.chatter >= 3 then Msg.message "Skipping query (bound = 0)\n"
        else begin
          if !Global.chatter >= 4 then Msg.message "skipping" else ()
        end
      end
      end;
      begin if !Global.chatter >= 3 then
        Msg.message "____________________________________________\n\n"
      else begin
        if !Global.chatter >= 4 then Msg.message " OK\n" else ()
      end
      end
    end

  (* optName = SOME(X) or NONE, Xs = free variables in query excluding X *)
  (* times itself *)
  (* Problem: we cannot give an answer substitution for the variables
         in the printed query, since the new variables in this query
         may not necessarily have global scope.

         For the moment, we print only the answer substitution for the
         original variables encountered during parsing.
       *)
  (* val Xs' = if !Global.chatter >= 3 then Names.namedEVars () else Xs
       *)
  (* solutions = ref <n> counts the number of solutions found *)
  (* Initial success continuation prints substitution (according to chatter level)
         and raises exception Done if bound has been reached, otherwise it returns
         to search for further solutions
       *)

  (* %query <expected> <try> A or %query <expected> <try> X : A *)
  let rec querySbt ((expected, try_, quy), Paths.Loc (fileName, r)) =
    let a_, optName, xs_ =
      ReconQuery.queryToQuery (quy, Paths.Loc (fileName, r))
    in
    let _ =
      begin if !Global.chatter >= 3 then
        Msg.message
          (((("%query " ^ boundToString expected) ^ " ") ^ boundToString try_)
          ^ "\n")
      else ()
      end
    in
    let _ =
      begin if !Global.chatter >= 4 then Msg.message " " else ()
      end
    in
    let _ =
      begin if !Global.chatter >= 3 then
        Msg.message
          (("\n" ^ Timers.time Timers.printing expToString (IntSyn.null_, a_))
          ^ ".\n")
      else ()
      end
    in
    let g =
      Timers.time Timers.compiling Compile.compileGoal (IntSyn.null_, a_)
    in
    let solutions = ref 0 in
    let rec scInit m_ =
      begin
        solutions := !solutions + 1;
        begin
          begin if !Global.chatter >= 3 then begin
            Msg.message
              (("---------- Solution " ^ Int.toString !solutions)
              ^ " ----------\n");
            Msg.message (Timers.time Timers.printing evarInstToString xs_ ^ "\n")
          end
          else begin
            if !Global.chatter >= 3 then Msg.message "." else ()
          end
          end;
          begin
            begin match optName with
            | None -> ()
            | Some name -> begin
                begin if !Global.chatter > 3 then begin
                  Msg.message "\n pskeleton \n";
                  Msg.message (CompSyn.pskeletonToString m_ ^ "\n")
                end
                else ()
                end;
                Timers.time Timers.ptrecon PtRecon.solve
                  ( m_,
                    (g, IntSyn.id),
                    CompSyn.DProg (IntSyn.null_, IntSyn.null_),
                    function
                    | pskel, m_ -> begin
                        if !Global.chatter >= 3 then
                          Msg.message
                            (Timers.time Timers.printing evarInstToString
                               [ (m_, name) ]
                            ^ "\n")
                        else ()
                      end )
              end
            end;
            begin
              begin if !Global.chatter >= 3 then begin
                match
                  Timers.time Timers.printing Print.evarCnstrsToStringOpt xs_
                with
                | None -> ()
                | Some str ->
                    Msg.message (("Remaining constraints:\n" ^ str) ^ "\n")
              end
              else ()
              end
              (* Question: should we collect constraints in M? *);
              begin if exceeds (Some !solutions, try_) then raise Done else ()
              end
            end
          end
        end
      end
    in
    let rec search () =
      AbsMachineSbt.solve
        ((g, IntSyn.id), CompSyn.DProg (IntSyn.null_, IntSyn.null_), scInit)
    in
    begin
      begin if not (boundEq (try_, Some 0)) then begin
        Cs_manager.reset ();
        begin try
          TimeLimit.timeLimit !Global.timeLimit
            (Timers.time Timers.solving search)
            ()
        with Done -> (
          try ()
          with timeOut_ ->
            raise (AbortQuery "\n----------- TIME OUT ---------------\n");
            begin
              Cs_manager.reset ();
              checkSolutions (expected, try_, !solutions)
            end)
        end
      end
      (* solve query if bound > 0 *)
      (* printing is timed into solving! *)
      (* in case Done was raised *)
      (* check if number of solutions is correct *)
        else begin
        if !Global.chatter >= 3 then Msg.message "Skipping query (bound = 0)\n"
        else begin
          if !Global.chatter >= 4 then Msg.message "skipping" else ()
        end
      end
      end;
      begin if !Global.chatter >= 3 then
        Msg.message "____________________________________________\n\n"
      else begin
        if !Global.chatter >= 4 then Msg.message " OK\n" else ()
      end
      end
    end

  (* optName = SOME(X) or NONE, Xs = free variables in query excluding X *)
  (* times itself *)
  (* Problem: we cannot give an answer substitution for the variables
               in the printed query, since the new variables in this query
               may not necessarily have global scope.

               For the moment, we print only the answer substitution for the
               original variables encountered during parsing.
             *)
  (*
                val Xs' = if !Global.chatter >= 3 then Names.namedEVars () else Xs
             *)
  (* solutions = ref <n> counts the number of solutions found *)
  (* Initial success continuation prints substitution (according to chatter level)
         and raises exception Done if bound has been reached, otherwise it returns
         to search for further solutions
       *)

  (* %query <expected> <try> A or %query <expected> <try> X : A  *)
  let rec query args =
    begin match !Compile.optimize with
    | indexing_ -> querySbt args
    | linearHeads_ -> query' args
    | _ -> query' args
    end
  (* Execute query where program clauses are
            indexed using substitution trees -- if we require the proof term X
            it will be reconstructed after the query A has succeeded - bp
          *)

  (* %querytabled <expected solutions> <max stages tried>  A
or  %querytabled <expected solutions> <max stages tried>  X : A
  note : %querytabled terminates if we have found the expected number of
  solutions or if we have reached the maximal number of stages *)
  let rec querytabled ((numSol, try_, quy), Paths.Loc (fileName, r)) =
    let _ =
      begin if !Global.chatter >= 3 then
        Msg.message
          ((("%querytabled " ^ boundToString numSol) ^ " ") ^ boundToString try_)
      else ()
      end
    in
    let a_, optName, xs_ =
      ReconQuery.queryToQuery (quy, Paths.Loc (fileName, r))
    in
    let _ =
      begin if !Global.chatter >= 4 then Msg.message " " else ()
      end
    in
    let _ =
      begin if !Global.chatter >= 3 then
        Msg.message
          (("\n" ^ Timers.time Timers.printing expToString (IntSyn.null_, a_))
          ^ ".\n")
      else ()
      end
    in
    let g =
      Timers.time Timers.compiling Compile.compileGoal (IntSyn.null_, a_)
    in
    let solutions = ref 0 in
    let status = ref false in
    let solExists = ref false in
    let stages = ref 1 in
    let rec scInit o_ =
      begin
        solutions := !solutions + 1;
        begin
          solExists := true;
          begin
            begin if !Global.chatter >= 3 then begin
              Msg.message
                (("\n---------- Solutions " ^ Int.toString !solutions)
                ^ " ----------\n");
              Msg.message
                (Timers.time Timers.printing evarInstToString xs_ ^ " \n")
            end
            else begin
              if !Global.chatter >= 1 then Msg.message "." else ()
            end
            end;
            begin
              begin match optName with
              | None -> ()
              | Some name -> begin
                  Msg.message (CompSyn.pskeletonToString o_ ^ "\n");
                  Timers.time Timers.ptrecon PtRecon.solve
                    ( o_,
                      (g, IntSyn.id),
                      CompSyn.DProg (IntSyn.null_, IntSyn.null_),
                      function
                      | o_, m_ -> begin
                          if !Global.chatter >= 3 then
                            Msg.message
                              (Timers.time Timers.printing evarInstToString
                                 [ (m_, name) ]
                              ^ "\n")
                          else ()
                        end )
                end
              end;
              begin
                begin if !Global.chatter >= 3 then begin
                  match
                    Timers.time Timers.printing Print.evarCnstrsToStringOpt xs_
                  with
                  | None -> ()
                  | Some str ->
                      Msg.message (("Remaining constraints:\n" ^ str) ^ "\n")
                end
                else ()
                end
                (* Question: should we collect constraints in M? *);
                begin
                  begin if !Global.chatter >= 1 then
                    Msg.message "More solutions?\n"
                  else ()
                  end;
                  begin match numSol with
                  | None -> ()
                  | Some n -> begin
                      if !solutions = n then begin
                        begin if !Global.chatter >= 1 then
                          Msg.message "Found enough solutions\n"
                        else ()
                        end;
                        raise Done
                      end
                      else ()
                    end
                  end
                end
              end
            end
          end
        end
      end
    in
    let rec loop () =
      begin
        begin if exceeds (Some (!stages - 1), try_) then begin
          begin if !Global.chatter >= 1 then
            Msg.message
              (("\n ================= " ^ " Number of tries exceeds stages ")
              ^ " ======================= \n")
          else ()
          end;
          begin
            status := false;
            raise Done
          end
        end
        else ()
        end;
        begin
          begin if !Global.chatter >= 1 then
            Msg.message
              (("\n ====================== Stage " ^ Int.toString !stages)
              ^ " finished =================== \n")
          else ()
          end;
          begin
            begin if exceeds (Some !stages, try_) then begin
              Msg.message
                (("\n ================= " ^ " Number of tries exceeds stages ")
                ^ " ======================= \n");
              begin
                status := false;
                raise Done
              end
            end
            else ()
            end;
            begin
              begin if Tabled.nextStage () then begin
                stages := !stages + 1;
                loop ()
              end
              else status := true
              end
              (* table did not change,
               * i.e. all solutions have been found
               * we check for *all* solutions
               *);
              raise Done
            end
          end
        end
      end
    in
    let _ = Tabled.reset () in
    let _ = Tabled.fillTable () in
    let rec tabledSearch () =
      begin
        Tabled.solve
          ((g, IntSyn.id), CompSyn.DProg (IntSyn.null_, IntSyn.null_), scInit);
        begin
          Cs_manager.reset ();
          begin
            loop ();
            checkStages (try_, !stages)
          end
        end
      end
      (* in case Done was raised *)
      (* next stage until table doesn't change *)
    in
    begin
      begin if not (boundEq (try_, Some 0)) then
        try
          begin
            Cs_manager.reset ();
            try
              TimeLimit.timeLimit !Global.timeLimit
                (Timers.time Timers.solving tabledSearch)
                ()
            with timeOut_ ->
              begin
                Msg.message "\n----------- TIME OUT ---------------\n";
                raise Done
              end
          end
          (* solve query if bound > 0 *)
        with Done -> ()
      else begin
        if !Global.chatter >= 3 then Msg.message "Skipping query (bound = 0)\n"
        else begin
          if !Global.chatter >= 2 then Msg.message "skipping" else ()
        end
      end
      end;
      begin
        begin if !Global.chatter >= 3 then begin
          Msg.message "\n____________________________________________\n\n";
          begin
            Msg.message
              ((((("number of stages: tried " ^ boundToString try_) ^ " \n")
                ^ "terminated after ")
               ^ Int.toString !stages)
              ^ " stages \n \n");
            begin
              begin if !solExists then ()
              else Msg.message "\nNO solution exists to query \n\n"
              end;
              begin
                begin if !status then
                  Msg.message "Tabled evaluation COMPLETE \n \n"
                else Msg.message "Tabled evaluation NOT COMPLETE \n \n"
                end;
                begin
                  Msg.message
                    "\n____________________________________________\n\n";
                  begin
                    Msg.message "\n Table Indexing parameters: \n";
                    begin
                      begin match !TableParam.strategy with
                      | variant_ ->
                          Msg.message "\n       Table Strategy := Variant \n"
                      | subsumption_ ->
                          Msg.message
                            "\n       Table Strategy := Subsumption \n"
                      end;
                      begin
                        begin if !TableParam.strengthen then
                          Msg.message "\n       Strengthening := true \n"
                        else Msg.message "\n       Strengthening := false \n"
                        end;
                        begin
                          Msg.message
                            (("\nNumber of table indices : "
                             ^ Int.toString (Tabled.tableSize ()))
                            ^ "\n");
                          begin
                            Msg.message
                              (("Number of suspended goals : "
                               ^ Int.toString (Tabled.suspGoalNo ()))
                              ^ "\n");
                            Msg.message
                              "\n\
                               ____________________________________________\n\n"
                          end
                        end
                      end
                    end
                  end
                end
              end
            end
          end
        end
        else begin
          if !Global.chatter >= 3 then Msg.message " OK\n" else ()
        end
        end;
        Tabled.updateGlobalTable (g, !status)
      end
    end

  (* optName = SOME(X) or NONE, Xs = free variables in query excluding X *)
  (* times itself *)
  (* Problem: we cannot give an answer substitution for the variables
        in the printed query, since the new variables in this query
        may not necessarily have global scope.

        For the moment, we print only the answer substitution for the
        original variables encountered during parsing.
     *)
  (* val Xs' = if !Global.chatter >= 3 then Names.namedEVars () else Xs *)
  (* solutions = ref <n> counts the number of solutions found *)
  (* stage = ref <n> counts the number of stages found *)
  (* Initial success continuation prints substitution (according to chatter level)
         and raises exception Done if bound has been reached, otherwise it returns
         to search for further solutions
       *)
  (* loops -- scinit will raise exception Done *)

  (* Interactive Query Top Level *)
  let rec qLoop () =
    qLoops
      begin
        Cs_manager.reset ();
        Parser.parseTerminalQ ("?- ", "   ")
      end

  and qLoops s = qLoops' (Timers.time Timers.parsing S.expose s)

  and qLoops' = function
    | empty_ -> true
    | S.Cons (query_, s') ->
        let a_, optName, xs_ =
          ReconQuery.queryToQuery (query_, Paths.Loc ("stdIn", Paths.Reg (0, 0)))
        in
        let g =
          Timers.time Timers.compiling Compile.compileGoal (IntSyn.null_, a_)
        in
        let rec scInit m_ =
          begin
            begin if !Global.chatter >= 1 then
              Msg.message
                (Timers.time Timers.printing evarInstToString xs_ ^ "\n")
            else ()
            end;
            begin
              begin match optName with
              | None -> ()
              | Some name -> begin
                  if !Global.chatter >= 3 then
                    Msg.message
                      (Timers.time Timers.printing evarInstToString
                         [ (m_, name) ]
                      ^ "\n")
                  else ()
                end
              end;
              begin
                begin if !Global.chatter >= 3 then begin
                  match
                    Timers.time Timers.printing Print.evarCnstrsToStringOpt xs_
                  with
                  | None -> ()
                  | Some str ->
                      Msg.message (("Remaining constraints:\n" ^ str) ^ "\n")
                end
                else ()
                end
                (* Question: should we collect constraints from M *);
                begin if moreSolutions () then () else raise Done
                end
              end
            end
          end
        in
        let _ =
          begin if !Global.chatter >= 3 then Msg.message "Solving...\n" else ()
          end
        in
        begin try
          begin
            Timers.time Timers.solving AbsMachine.solve
              ( (g, IntSyn.id),
                CompSyn.DProg (IntSyn.null_, IntSyn.null_),
                scInit );
            Msg.message "No more solutions\n";
            qLoop ()
          end
          (* scInit is timed into solving! *)
        with Done ->
          ();
          qLoop ()
        end

  (* times itself *)
  (* Ignore s': parse one query at a time *)
  (* normal exit *)

  (* primary, secondary prompt *)
  (* querytabled interactive top loop *)
  let rec qLoopT () =
    qLoopsT
      begin
        Cs_manager.reset ();
        Parser.parseTerminalQ ("?- ", "   ")
      end

  and qLoopsT s = qLoopsT' (Timers.time Timers.parsing S.expose s)

  and qLoopsT' = function
    | empty_ -> true
    | S.Cons (query_, s') ->
        let solExists = ref false in
        let a_, optName, xs_ =
          ReconQuery.queryToQuery (query_, Paths.Loc ("stdIn", Paths.Reg (0, 0)))
        in
        let g =
          Timers.time Timers.compiling Compile.compileGoal (IntSyn.null_, a_)
        in
        let _ = Tabled.reset () in
        let rec scInit o_ =
          begin
            begin if !Global.chatter >= 1 then
              Msg.message
                (Timers.time Timers.printing evarInstToString xs_ ^ "\n")
            else ()
            end;
            begin
              begin match optName with
              | None -> ()
              | Some name -> begin
                  if !Global.chatter >= 3 then
                    Msg.message
                      " Sorry cannot reconstruct pskeleton proof terms yet \n"
                  else ()
                end
              end;
              begin
                begin if !Global.chatter >= 3 then begin
                  match
                    Timers.time Timers.printing Print.evarCnstrsToStringOpt xs_
                  with
                  | None -> ()
                  | Some str ->
                      Msg.message (("Remaining constraints:\n" ^ str) ^ "\n")
                end
                else ()
                end
                (* Question: should we collect constraints from M? *);
                begin
                  solExists := true;
                  begin if moreSolutions () then () else raise Done
                  end
                end
              end
            end
          end
        in
        let rec loop () =
          begin if Tabled.nextStage () then loop () else raise Completed
          end
          (* table did not change,
           * i.e. all solutions have been found
           * we check for *all* solutions
           *)
        in
        let _ =
          begin if !Global.chatter >= 3 then Msg.message "Solving...\n" else ()
          end
        in
        begin try
          begin
            Timers.time Timers.solving Tabled.solve
              ( (g, IntSyn.id),
                CompSyn.DProg (IntSyn.null_, IntSyn.null_),
                scInit );
            try loop ()
            with Completed ->
              begin if !solExists then Msg.message "No more solutions\n"
              else Msg.message "the query has no solution\n"
              end;
              qLoopT ()
          end
          (* scInit is timed into solving! *)
        with Done ->
          ();
          qLoopT ()
        end
  (* times itself *)
  (* loops -- scinit will raise exception Done *)
  (* Ignore s': parse one query at a time *)
  (* normal exit *)
  (* primary, secondary prompt *)
end
(* functor Solve *)

(* # 1 "src/frontend/solve.sml.ml" *)
