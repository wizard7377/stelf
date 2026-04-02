(* # 1 "src/server/Server_.sig.ml" *)

(* # 1 "src/server/Server_.fun.ml" *)

(* # 1 "src/server/Server_.sml.ml" *)
open! Basis

(** Interactive command server for Stelf/STELF. *)
include Server_intf
(* signature SERVER *)
module Server : SERVER = struct
  let globalConfig : Stelf.Config.config option ref = ref None

  (* readLine () = (command, args)
     reads a command and and its arguments from the command line.
  *)
  let rec readLine () =
    let rec inputLine97 ins =
      begin match TextIO.inputLine ins with Some line -> line | None -> ""
      end
    in
    let rec getLine () =
      try inputLine97 TextIO.stdIn with OS.SysErr (_, Some _) -> getLine ()
    in
    let line = getLine () in
    let rec triml ss = Substring.dropl Char.isSpace ss in
    let rec trimr ss = Substring.dropr Char.isSpace ss in
    let line' = triml (trimr (Substring.full line)) in
    begin if line = "" then ("OS.exit", "")
    else begin
      if Substring.size line' = 0 then readLine ()
      else
        let command', args' = Substring.position " " line' in
        (Substring.string command', Substring.string (triml args'))
    end
    end

  (* val line = TextIO.inputLine (TextIO.stdIn) *)
  (* Fix for MLton, Fri Dec 20 21:50:22 2002 -sweeks (fp) *)

  (* tokenize (args) = [token1, token2, ..., tokenn]
     splits the arguments string into a list of space-separated
     tokens
  *)
  let tokenize args = String.tokens Char.isSpace args

  (* exception Error for server errors *)
  exception Error of string

  let error msg = raise (Error msg)
  let quote string = ("`" ^ string) ^ "'"

  (* Print the OK or ABORT messages which are parsed by Emacs *)
  let issue = function
    | Stelf.Ok -> print "%% OK %%\n"
    | Stelf.Abort -> print "%% ABORT %%\n"

  (* Checking if there are no extraneous arguments *)
  let check_empty = function "" -> () | args -> error "Extraneous arguments"

  (* Command argument types *)
  (* File names, given a default *)
  let get_file = function
    | "", default -> default
    | fileName, default -> fileName

  (* File names, not defaults *)
  let get_file_required = function
    | "" -> error "Missing filename"
    | fileName -> fileName

  (* Identifiers, used as a constant *)
  let get_id = function
    | id :: [] -> Stdlib.String.trim id
    | [] -> error "Missing identifier"
    | ts -> error "Extraneous arguments"

  (* Identifiers, used as a trace specification *)
  let get_ids ids = ids

  (* Strategies for %prove, %establish *)
  let get_strategy = function
    | "FRS" :: [] -> Stelf.Prover.Frs
    | "RFS" :: [] -> Stelf.Prover.Rfs
    | [] -> error "Missing strategy"
    | t :: [] -> error (quote t ^ " is not a strategy (must be FRS or RFS)")
    | ts -> error "Extraneous arguments"

  let strategy_to_string = function
    | Stelf.Prover.Frs -> "FRS"
    | Stelf.Prover.Rfs -> "RFS"

  (* Booleans *)
  let get_bool = function
    | "true" :: [] -> true
    | "false" :: [] -> false
    | [] -> error "Missing boolean value"
    | t :: [] -> error (quote t ^ " is not a boolean")
    | ts -> error "Extraneous arguments"

  (* Natural numbers *)
  let get_nat = function
    | t :: [] -> (
        match Int.fromString t with
        | Some n when n >= 0 -> n
        | _ -> error (quote t ^ " is not a natural number"))

  (* Limits ( *, or natural number) *)
  let get_limit = function
    | "*" :: [] -> None
    | t :: ts -> Some (get_nat (t :: ts))
    | [] -> error "Missing `*' or natural number"

  let limit_to_string = function None -> "*" | Some i -> Int.toString i

  (* Tabling strategy *)
  let get_table_strategy = function
    | "Variant" :: [] -> Stelf.Table.Variant
    | "Subsumption" :: [] -> Stelf.Table.Subsumption
    | [] -> error "Missing tabling strategy"
    | t :: [] ->
        error
          (quote t
         ^ " is not a tabling strategy (must be Variant or Subsumption)")
    | ts -> error "Extraneous arguments"

  let table_strategy_to_string = function
    | Stelf.Table.Variant -> "Variant"
    | Stelf.Table.Subsumption -> "Subsumption"

  (* Tracing mode for term reconstruction *)
  let get_recon_trace_mode = function
    | "Progressive" :: [] -> Stelf.Recon.Progressive
    | "Omniscient" :: [] -> Stelf.Recon.Omniscient
    | [] -> error "Missing tracing reconstruction mode"
    | t :: [] ->
        error
          (quote t
         ^ " is not a tracing reconstruction mode\n\
            (must be Progressive or Omniscient)")
    | ts -> error "Extraneous arguments"

  let recon_trace_mode_to_string = function
    | Stelf.Recon.Progressive -> "Progressive"
    | Stelf.Recon.Omniscient -> "Omniscient"

  (* Compile options *)
  let get_compile_opt = function
    | "No" :: [] -> Stelf.Compile.No
    | "LinearHeads" :: [] -> Stelf.Compile.LinearHeads
    | "Indexing" :: [] -> Stelf.Compile.Indexing
    | [] -> error "Missing tabling strategy"
    | t :: [] ->
        error
          (quote t
         ^ " is not a compile option (must be No, LinearHeads, or Indexing ")
    | ts -> error "Extraneous arguments"

  let comp_opt_to_string = function
    | Stelf.Compile.No -> "No"
    | Stelf.Compile.LinearHeads -> "LinearHeads"
    | Stelf.Compile.Indexing -> "Indexing"

  (* Setting Stelf parameters *)
  let set_parm = function
    | "chatter" :: ts -> Stelf.chatter := get_nat ts
    | "doubleCheck" :: ts -> Stelf.doubleCheck := get_bool ts
    | "unsafe" :: ts -> Stelf.unsafe := get_bool ts
    | "autoFreeze" :: ts -> Stelf.autoFreeze := get_bool ts
    | "Print.implicit" :: ts -> Stelf.Print.implicit := get_bool ts
    | "Print.depth" :: ts -> Stelf.Print.depth := get_limit ts
    | "Print.length" :: ts -> Stelf.Print.length := get_limit ts
    | "Print.indent" :: ts -> Stelf.Print.indent := get_nat ts
    | "Print.width" :: ts -> Stelf.Print.width := get_nat ts
    | "Trace.detail" :: ts -> Stelf.Trace.detail := get_nat ts
    | "Compile.optimize" :: ts -> Stelf.Compile.optimize := get_compile_opt ts
    | "Recon.trace" :: ts -> Stelf.Recon.trace := get_bool ts
    | "Recon.traceMode" :: ts ->
        Stelf.Recon.traceMode := get_recon_trace_mode ts
    | "Prover.strategy" :: ts -> Stelf.Prover.strategy := get_strategy ts
    | "Prover.maxSplit" :: ts -> Stelf.Prover.maxSplit := get_nat ts
    | "Prover.maxRecurse" :: ts -> Stelf.Prover.maxRecurse := get_nat ts
    | "Table.strategy" :: ts -> Stelf.Table.strategy := get_table_strategy ts
    | "Table.strengthen" :: ts -> Stelf.Table.strengthen := get_bool ts
    | t :: ts -> error ("Unknown parameter " ^ quote t)
    | [] -> error "Missing parameter"

  (* Getting Stelf parameter values *)
  let get_parm = function
    | "chatter" :: ts -> Int.toString !Stelf.chatter
    | "doubleCheck" :: ts -> Bool.toString !Stelf.doubleCheck
    | "unsafe" :: ts -> Bool.toString !Stelf.unsafe
    | "autoFreeze" :: ts -> Bool.toString !Stelf.autoFreeze
    | "Print.implicit" :: ts -> Bool.toString !Stelf.Print.implicit
    | "Print.depth" :: ts -> limit_to_string !Stelf.Print.depth
    | "Print.length" :: ts -> limit_to_string !Stelf.Print.length
    | "Print.indent" :: ts -> Int.toString !Stelf.Print.indent
    | "Print.width" :: ts -> Int.toString !Stelf.Print.width
    | "Trace.detail" :: ts -> Int.toString !Stelf.Trace.detail
    | "Compile.optimize" :: ts -> comp_opt_to_string !Stelf.Compile.optimize
    | "Recon.trace" :: ts -> Bool.toString !Stelf.Recon.trace
    | "Recon.traceMode" :: ts ->
        recon_trace_mode_to_string !Stelf.Recon.traceMode
    | "Prover.strategy" :: ts -> strategy_to_string !Stelf.Prover.strategy
    | "Prover.maxSplit" :: ts -> Int.toString !Stelf.Prover.maxSplit
    | "Prover.maxRecurse" :: ts -> Int.toString !Stelf.Prover.maxRecurse
    | "Table.strategy" :: ts -> table_strategy_to_string !Stelf.Table.strategy
    | t :: ts -> error ("Unknown parameter " ^ quote t)
    | [] -> error "Missing parameter"

  (* extracted from doc/guide/stelf.texi *)
  let helpString =
    "Commands:\n\
    \  set <parameter> <value>     - Set <parameter> to <value>\n\
    \  get <parameter>             - Print the current value of <parameter>\n\
    \  Trace.trace <id1> ... <idn> - Trace given constants\n\
    \  Trace.traceAll              - Trace all constants\n\
    \  Trace.untrace               - Untrace all constants\n\
    \  Trace.break <id1> ... <idn> - Set breakpoint for given constants\n\
    \  Trace.breakAll              - Break on all constants\n\
    \  Trace.unbreak               - Remove all breakpoints\n\
    \  Trace.show                  - Show current trace and breakpoints\n\
    \  Trace.reset                 - Reset all tracing and breaking\n\
    \  Print.sgn                   - Print current signature\n\
    \  Print.prog                  - Print current signature as program\n\
    \  Print.subord                - Print current subordination relation\n\
    \  Print.domains               - Print registered constraint domains\n\
    \  Print.TeX.sgn               - Print signature in TeX format\n\
    \  Print.TeX.prog              - Print signature in TeX format as program\n\
    \  Timers.show                 - Print and reset timers\n\
    \  Timers.reset                - Reset timers\n\
    \  Timers.check                - Print, but do not reset Timers.\n\
    \  OS.chDir <file>             - Change working directory to <file>\n\
    \  OS.getDir                   - Print current working directory\n\
    \  OS.exit                     - Exit Stelf server\n\
    \  quit                        - Quit Stelf server (same as exit)\n\
    \  Config.read <file>          - Read current configuration from <file>\n\
    \  Config.load                 - Load current configuration\n\
    \  Config.append               - Load current configuration without prior \
     reset\n\
    \  make <file>                 - Read and load configuration from <file>\n\
    \  reset                       - Reset global signature.\n\
    \  loadFile <file>             - Load Stelf file <file>\n\
    \  decl <id>                   - Show constant declaration for <id>\n\
    \  top                         - Enter interactive query loop\n\
    \  Table.top                   - Enter interactive loop for tables queries\n\
    \  version                     - Print Stelf server's version\n\
    \  help                        - Print this help message\n\n\
     Parameters:\n\
    \  chatter <nat>               - Level of verbosity (0 = none, 3 = default)\n\
    \  doubleCheck <bool>          - Perform additional internal type-checking\n\
    \  unsafe <bool>               - Allow unsafe operations (%assert)\n\
    \  autoFreeze <bool>           - Freeze families involved in meta-theorems\n\
    \  Print.implicit <bool>       - Print implicit arguments\n\
    \  Print.depth <limit>         - Cut off printing at depth <limit>\n\
    \  Print.length <limit>        - Cut off printing at length <limit>\n\
    \  Print.indent <nat>          - Indent by <nat> spaces\n\
    \  Print.width <nat>           - Line width for formatting\n\
    \  Trace.detail <nat>          - Detail of tracing\n\
    \  Compile.optimize <bool>     - Optimize during translation to clauses\n\
    \  Recon.trace <bool>          - Trace term reconstruction\n\
    \  Recon.traceMode <reconTraceMode> - Term reconstruction tracing mode\n\
    \  Prover.strategy <strategy>  - Prover strategy\n\
    \  Prover.maxSplit <nat>       - Prover splitting depth bound\n\
    \  Prover.maxRecurse <nat>     - Prover recursion depth bound\n\
    \  Table.strategy <tableStrategy>   - Tabling strategy\n\n\
     Server types:\n\
    \  file                        - File name, relative to working directory\n\
    \  id                          - A Stelf identifier\n\
    \  bool                        - Either `true' or `false'\n\
    \  nat                         - A natural number (starting at `0')\n\
    \  limit                       - Either `*' (no limit) or a natural number\n\
    \  reconTraceMode              - Either `Progressive' or `Omniscient'\n\
    \  strategy                    - Either `FRS' or `RFS'\n\
    \  tableStrategy               - Either `Variant' or `Subsumption'\n\n\
     See http://www.Cs.cmu.edu/~stelf/guide-1-4/ for more information,\n\
     or type M-x stelf-info (C-c C-h) in Emacs.\n"

  let rec serve' = function
    | "set", args -> begin
        set_parm (tokenize args);
        serve Stelf.Ok
      end
    | "get", args -> begin
        print (get_parm (tokenize args) ^ "\n");
        serve Stelf.Ok
      end
    | "Style.check", args -> begin
        check_empty args;
        begin
          ();
          serve Stelf.Ok
        end
      end
    | "Print.sgn", args -> begin
        check_empty args;
        begin
          Stelf.Print.sgn ();
          serve Stelf.Ok
        end
      end
    | "Print.prog", args -> begin
        check_empty args;
        begin
          Stelf.Print.prog ();
          serve Stelf.Ok
        end
      end
    | "Print.subord", args -> begin
        check_empty args;
        begin
          Stelf.Print.subord ();
          serve Stelf.Ok
        end
      end
    | "Print.domains", args -> begin
        check_empty args;
        begin
          Stelf.Print.domains ();
          serve Stelf.Ok
        end
      end
    | "Print.TeX.sgn", args -> begin
        check_empty args;
        begin
          Stelf.Print.TeX.sgn ();
          serve Stelf.Ok
        end
      end
    | "Print.TeX.prog", args -> begin
        check_empty args;
        begin
          Stelf.Print.TeX.prog ();
          serve Stelf.Ok
        end
      end
    | "Trace.trace", args -> begin
        Stelf.Trace.trace (Stelf.Trace.Some (get_ids (tokenize args)));
        serve Stelf.Ok
      end
    | "Trace.traceAll", args -> begin
        check_empty args;
        begin
          Stelf.Trace.trace Stelf.Trace.All;
          serve Stelf.Ok
        end
      end
    | "Trace.untrace", args -> begin
        check_empty args;
        begin
          Stelf.Trace.trace Stelf.Trace.None;
          serve Stelf.Ok
        end
      end
    | "Trace.break", args -> begin
        Stelf.Trace.break (Stelf.Trace.Some (get_ids (tokenize args)));
        serve Stelf.Ok
      end
    | "Trace.breakAll", args -> begin
        check_empty args;
        begin
          Stelf.Trace.break Stelf.Trace.All;
          serve Stelf.Ok
        end
      end
    | "Trace.unbreak", args -> begin
        check_empty args;
        begin
          Stelf.Trace.break Stelf.Trace.None;
          serve Stelf.Ok
        end
      end
    | "Trace.show", args -> begin
        check_empty args;
        begin
          Stelf.Trace.show ();
          serve Stelf.Ok
        end
      end
    | "Trace.reset", args -> begin
        check_empty args;
        begin
          Stelf.Trace.reset ();
          serve Stelf.Ok
        end
      end
    | "Timers.show", args -> begin
        check_empty args;
        begin
          Stelf.Timers.show ();
          serve Stelf.Ok
        end
      end
    | "Timers.reset", args -> begin
        check_empty args;
        begin
          Stelf.Timers.reset ();
          serve Stelf.Ok
        end
      end
    | "Timers.check", args -> begin
        check_empty args;
        begin
          Stelf.Timers.check ();
          serve Stelf.Ok
        end
      end
    | "OS.chDir", args -> begin
        Stelf.OS.chDir (get_file_required args);
        serve Stelf.Ok
      end
    | "OS.getDir", args -> begin
        check_empty args;
        begin
          print (Stelf.OS.getDir () ^ "\n");
          serve Stelf.Ok
        end
      end
    | "OS.exit", args -> begin
        check_empty args;
        ()
      end
    | "quit", args -> ()
    | "Config.read", args ->
        let fileName = get_file (args, "sources.cfg") in
        begin
          globalConfig := Some (Stelf.Config.read fileName);
          serve Stelf.Ok
        end
    | "Config.load", args -> begin
        begin match !globalConfig with
        | None -> globalConfig := Some (Stelf.Config.read "sources.cfg")
        | _ -> ()
        end;
        serve (Stelf.Config.load (valOf !globalConfig))
      end
    | "Config.append", args -> begin
        begin match !globalConfig with
        | None -> globalConfig := Some (Stelf.Config.read "sources.cfg")
        | _ -> ()
        end;
        serve (Stelf.Config.append (valOf !globalConfig))
      end
    | "make", args ->
        let fileName = get_file (args, "sources.cfg") in
        begin
          globalConfig := Some (Stelf.Config.read fileName);
          serve (Stelf.Config.load (valOf !globalConfig))
        end
    | "reset", args -> begin
        check_empty args;
        begin
          Stelf.reset ();
          serve Stelf.Ok
        end
      end
    | "loadFile", args -> serve (Stelf.loadFile (get_file_required args))
    | "readDecl", args -> begin
        check_empty args;
        serve (Stelf.readDecl ())
      end
    | "decl", args -> serve (Stelf.decl (get_id (tokenize args)))
    | "top", args -> begin
        check_empty args;
        begin
          Stelf.top ();
          serve Stelf.Ok
        end
      end
    | "Table.top", args -> begin
        check_empty args;
        begin
          Stelf.Table.top ();
          serve Stelf.Ok
        end
      end
    | "version", args -> begin
        print (Stelf.version ^ "\n");
        serve Stelf.Ok
      end
    | "help", args -> begin
        print helpString;
        serve Stelf.Ok
      end
    | t, args -> error ("Unrecognized command " ^ quote t)

  and serveLine () = serve' (readLine ())

  and serve = function
    | Stelf.Ok -> begin
        issue Stelf.Ok;
        serveLine ()
      end
    | Stelf.Abort -> begin
        issue Stelf.Abort;
        serveLine ()
      end

  let rec serveTop status =
    try serve status with
    | Error msg -> begin
        print (("Server error: " ^ msg) ^ "\n");
        serveTop Stelf.Abort
      end
    | exn -> begin
        print (("Uncaught exception: " ^ exnMessage exn) ^ "\n");
        serveTop Stelf.Abort
      end

  let rec server (name, _) =
    begin
      print (Stelf.version ^ "\n");
      begin
        Timing.init ();
        begin
          serveTop Stelf.Ok;
          OS.Process.success
        end
      end
    end
end

(* serve' (command, args) = ()
     executes the server commands represented by `tokens', 
     issues success or failure and then reads another command line.
     Invariant: tokens must be non-empty.

     All input for one command must be on the same line.
  *)
(*
      serve' (""toc"", args) = error ""NYI""
    | serve' (""list-program"", args) = error ""NYI""
    | serve' (""list-signature"", args) = error ""NYI""
    *)
(* | serve' (""type-at"", args) = error ""NYI"" *)
(* | serve' (""complete-at"", args) = error ""NYI"" *)
(* quit, as a concession *)
(* ignore server name and arguments *)
(* initialize timers *)
