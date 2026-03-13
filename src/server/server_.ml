(* # 1 "src/server/server_.sig.ml" *)

(* # 1 "src/server/server_.fun.ml" *)

(* # 1 "src/server/server_.sml.ml" *)
open! Basis

module type SERVER = sig
  val server : string * string list -> OS.Process.status
end

(* signature SERVER *)
module Server : SERVER = struct
  let globalConfig : Twelf.Config.config option ref = ref None

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
  let rec tokenize args = String.tokens Char.isSpace args

  (* exception Error for server errors *)
  exception Error of string

  let rec error msg = raise (Error msg)
  let rec quote string = ("`" ^ string) ^ "'"

  (* Print the OK or ABORT messages which are parsed by Emacs *)
  let rec issue = function
    | Twelf.Ok -> print "%% OK %%\n"
    | Twelf.Abort -> print "%% ABORT %%\n"

  (* Checking if there are no extraneous arguments *)
  let rec checkEmpty = function
    | "" -> ()
    | args -> error "Extraneous arguments"

  (* Command argument types *)
  (* File names, given a default *)
  let rec getFile = function
    | "", default -> default
    | fileName, default -> fileName

  (* File names, not defaults *)
  let rec getFile' = function
    | "" -> error "Missing filename"
    | fileName -> fileName

  (* Identifiers, used as a constant *)
  let rec getId = function
    | id :: [] -> id
    | [] -> error "Missing identifier"
    | ts -> error "Extraneous arguments"

  (* Identifiers, used as a trace specification *)
  let rec getIds ids = ids

  (* Strategies for %prove, %establish *)
  let rec getStrategy = function
    | "FRS" :: [] -> Twelf.Prover.Frs
    | "RFS" :: [] -> Twelf.Prover.Rfs
    | [] -> error "Missing strategy"
    | t :: [] -> error (quote t ^ " is not a strategy (must be FRS or RFS)")
    | ts -> error "Extraneous arguments"

  let rec strategyToString = function
    | Twelf.Prover.Frs -> "FRS"
    | Twelf.Prover.Rfs -> "RFS"

  (* Booleans *)
  let rec getBool = function
    | "true" :: [] -> true
    | "false" :: [] -> false
    | [] -> error "Missing boolean value"
    | t :: [] -> error (quote t ^ " is not a boolean")
    | ts -> error "Extraneous arguments"

  (* Natural numbers *)
  let rec getNat = function
    | t :: [] -> (
        match Int.fromString t with
        | Some n when n >= 0 -> n
        | _ -> error (quote t ^ " is not a natural number"))

  (* Limits ( *, or natural number) *)
  let rec getLimit = function
    | "*" :: [] -> None
    | t :: ts -> Some (getNat (t :: ts))
    | [] -> error "Missing `*' or natural number"

  let rec limitToString = function None -> "*" | Some i -> Int.toString i

  (* Tabling strategy *)
  let rec getTableStrategy = function
    | "Variant" :: [] -> Twelf.Table.Variant
    | "Subsumption" :: [] -> Twelf.Table.Subsumption
    | [] -> error "Missing tabling strategy"
    | t :: [] ->
        error
          (quote t
         ^ " is not a tabling strategy (must be Variant or Subsumption)")
    | ts -> error "Extraneous arguments"

  let rec tableStrategyToString = function
    | Twelf.Table.Variant -> "Variant"
    | Twelf.Table.Subsumption -> "Subsumption"

  (* Tracing mode for term reconstruction *)
  let rec getReconTraceMode = function
    | "Progressive" :: [] -> Twelf.Recon.Progressive
    | "Omniscient" :: [] -> Twelf.Recon.Omniscient
    | [] -> error "Missing tracing reconstruction mode"
    | t :: [] ->
        error
          (quote t
         ^ " is not a tracing reconstruction mode\n\
            (must be Progressive or Omniscient)")
    | ts -> error "Extraneous arguments"

  let rec reconTraceModeToString = function
    | Twelf.Recon.Progressive -> "Progressive"
    | Twelf.Recon.Omniscient -> "Omniscient"

  (* Compile options *)
  let rec getCompileOpt = function
    | "No" :: [] -> Twelf.Compile.No
    | "LinearHeads" :: [] -> Twelf.Compile.LinearHeads
    | "Indexing" :: [] -> Twelf.Compile.Indexing
    | [] -> error "Missing tabling strategy"
    | t :: [] ->
        error
          (quote t
         ^ " is not a compile option (must be No, LinearHeads, or Indexing ")
    | ts -> error "Extraneous arguments"

  let rec compOptToString = function
    | Twelf.Compile.No -> "No"
    | Twelf.Compile.LinearHeads -> "LinearHeads"
    | Twelf.Compile.Indexing -> "Indexing"

  (* Setting Twelf parameters *)
  let rec setParm = function
    | "chatter" :: ts -> Twelf.chatter := getNat ts
    | "doubleCheck" :: ts -> Twelf.doubleCheck := getBool ts
    | "unsafe" :: ts -> Twelf.unsafe := getBool ts
    | "autoFreeze" :: ts -> Twelf.autoFreeze := getBool ts
    | "Print.implicit" :: ts -> Twelf.Print.implicit := getBool ts
    | "Print.depth" :: ts -> Twelf.Print.depth := getLimit ts
    | "Print.length" :: ts -> Twelf.Print.length := getLimit ts
    | "Print.indent" :: ts -> Twelf.Print.indent := getNat ts
    | "Print.width" :: ts -> Twelf.Print.width := getNat ts
    | "Trace.detail" :: ts -> Twelf.Trace.detail := getNat ts
    | "Compile.optimize" :: ts -> Twelf.Compile.optimize := getCompileOpt ts
    | "Recon.trace" :: ts -> Twelf.Recon.trace := getBool ts
    | "Recon.traceMode" :: ts -> Twelf.Recon.traceMode := getReconTraceMode ts
    | "Prover.strategy" :: ts -> Twelf.Prover.strategy := getStrategy ts
    | "Prover.maxSplit" :: ts -> Twelf.Prover.maxSplit := getNat ts
    | "Prover.maxRecurse" :: ts -> Twelf.Prover.maxRecurse := getNat ts
    | "Table.strategy" :: ts -> Twelf.Table.strategy := getTableStrategy ts
    | "Table.strengthen" :: ts -> Twelf.Table.strengthen := getBool ts
    | t :: ts -> error ("Unknown parameter " ^ quote t)
    | [] -> error "Missing parameter"

  (* Getting Twelf parameter values *)
  let rec getParm = function
    | "chatter" :: ts -> Int.toString !Twelf.chatter
    | "doubleCheck" :: ts -> Bool.toString !Twelf.doubleCheck
    | "unsafe" :: ts -> Bool.toString !Twelf.unsafe
    | "autoFreeze" :: ts -> Bool.toString !Twelf.autoFreeze
    | "Print.implicit" :: ts -> Bool.toString !Twelf.Print.implicit
    | "Print.depth" :: ts -> limitToString !Twelf.Print.depth
    | "Print.length" :: ts -> limitToString !Twelf.Print.length
    | "Print.indent" :: ts -> Int.toString !Twelf.Print.indent
    | "Print.width" :: ts -> Int.toString !Twelf.Print.width
    | "Trace.detail" :: ts -> Int.toString !Twelf.Trace.detail
    | "Compile.optimize" :: ts -> compOptToString !Twelf.Compile.optimize
    | "Recon.trace" :: ts -> Bool.toString !Twelf.Recon.trace
    | "Recon.traceMode" :: ts -> reconTraceModeToString !Twelf.Recon.traceMode
    | "Prover.strategy" :: ts -> strategyToString !Twelf.Prover.strategy
    | "Prover.maxSplit" :: ts -> Int.toString !Twelf.Prover.maxSplit
    | "Prover.maxRecurse" :: ts -> Int.toString !Twelf.Prover.maxRecurse
    | "Table.strategy" :: ts -> tableStrategyToString !Twelf.Table.strategy
    | t :: ts -> error ("Unknown parameter " ^ quote t)
    | [] -> error "Missing parameter"

  (* extracted from doc/guide/twelf.texi *)
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
    \  Timers.check                - Print, but do not reset timers.\n\
    \  OS.chDir <file>             - Change working directory to <file>\n\
    \  OS.getDir                   - Print current working directory\n\
    \  OS.exit                     - Exit Twelf server\n\
    \  quit                        - Quit Twelf server (same as exit)\n\
    \  Config.read <file>          - Read current configuration from <file>\n\
    \  Config.load                 - Load current configuration\n\
    \  Config.append               - Load current configuration without prior \
     reset\n\
    \  make <file>                 - Read and load configuration from <file>\n\
    \  reset                       - Reset global signature.\n\
    \  loadFile <file>             - Load Twelf file <file>\n\
    \  decl <id>                   - Show constant declaration for <id>\n\
    \  top                         - Enter interactive query loop\n\
    \  Table.top                   - Enter interactive loop for tables queries\n\
    \  version                     - Print Twelf server's version\n\
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
    \  id                          - A Twelf identifier\n\
    \  bool                        - Either `true' or `false'\n\
    \  nat                         - A natural number (starting at `0')\n\
    \  limit                       - Either `*' (no limit) or a natural number\n\
    \  reconTraceMode              - Either `Progressive' or `Omniscient'\n\
    \  strategy                    - Either `FRS' or `RFS'\n\
    \  tableStrategy               - Either `Variant' or `Subsumption'\n\n\
     See http://www.cs.cmu.edu/~twelf/guide-1-4/ for more information,\n\
     or type M-x twelf-info (C-c C-h) in Emacs.\n"

  let rec serve' = function
    | "set", args -> begin
        setParm (tokenize args);
        serve Twelf.Ok
      end
    | "get", args -> begin
        print (getParm (tokenize args) ^ "\n");
        serve Twelf.Ok
      end
    | "Style.check", args -> begin
        checkEmpty args;
        begin
          ();
          serve Twelf.Ok
        end
      end
    | "Print.sgn", args -> begin
        checkEmpty args;
        begin
          Twelf.Print.sgn ();
          serve Twelf.Ok
        end
      end
    | "Print.prog", args -> begin
        checkEmpty args;
        begin
          Twelf.Print.prog ();
          serve Twelf.Ok
        end
      end
    | "Print.subord", args -> begin
        checkEmpty args;
        begin
          Twelf.Print.subord ();
          serve Twelf.Ok
        end
      end
    | "Print.domains", args -> begin
        checkEmpty args;
        begin
          Twelf.Print.domains ();
          serve Twelf.Ok
        end
      end
    | "Print.TeX.sgn", args -> begin
        checkEmpty args;
        begin
          Twelf.Print.TeX.sgn ();
          serve Twelf.Ok
        end
      end
    | "Print.TeX.prog", args -> begin
        checkEmpty args;
        begin
          Twelf.Print.TeX.prog ();
          serve Twelf.Ok
        end
      end
    | "Trace.trace", args -> begin
        Twelf.Trace.trace (Twelf.Trace.Some (getIds (tokenize args)));
        serve Twelf.Ok
      end
    | "Trace.traceAll", args -> begin
        checkEmpty args;
        begin
          Twelf.Trace.trace Twelf.Trace.All;
          serve Twelf.Ok
        end
      end
    | "Trace.untrace", args -> begin
        checkEmpty args;
        begin
          Twelf.Trace.trace Twelf.Trace.None;
          serve Twelf.Ok
        end
      end
    | "Trace.break", args -> begin
        Twelf.Trace.break (Twelf.Trace.Some (getIds (tokenize args)));
        serve Twelf.Ok
      end
    | "Trace.breakAll", args -> begin
        checkEmpty args;
        begin
          Twelf.Trace.break Twelf.Trace.All;
          serve Twelf.Ok
        end
      end
    | "Trace.unbreak", args -> begin
        checkEmpty args;
        begin
          Twelf.Trace.break Twelf.Trace.None;
          serve Twelf.Ok
        end
      end
    | "Trace.show", args -> begin
        checkEmpty args;
        begin
          Twelf.Trace.show ();
          serve Twelf.Ok
        end
      end
    | "Trace.reset", args -> begin
        checkEmpty args;
        begin
          Twelf.Trace.reset ();
          serve Twelf.Ok
        end
      end
    | "Timers.show", args -> begin
        checkEmpty args;
        begin
          Twelf.Timers.show ();
          serve Twelf.Ok
        end
      end
    | "Timers.reset", args -> begin
        checkEmpty args;
        begin
          Twelf.Timers.reset ();
          serve Twelf.Ok
        end
      end
    | "Timers.check", args -> begin
        checkEmpty args;
        begin
          Twelf.Timers.check ();
          serve Twelf.Ok
        end
      end
    | "OS.chDir", args -> begin
        Twelf.OS.chDir (getFile' args);
        serve Twelf.Ok
      end
    | "OS.getDir", args -> begin
        checkEmpty args;
        begin
          print (Twelf.OS.getDir () ^ "\n");
          serve Twelf.Ok
        end
      end
    | "OS.exit", args -> begin
        checkEmpty args;
        ()
      end
    | "quit", args -> ()
    | "Config.read", args ->
        let fileName = getFile (args, "sources.cfg") in
        begin
          globalConfig := Some (Twelf.Config.read fileName);
          serve Twelf.Ok
        end
    | "Config.load", args -> begin
        begin match !globalConfig with
        | None -> globalConfig := Some (Twelf.Config.read "sources.cfg")
        | _ -> ()
        end;
        serve (Twelf.Config.load (valOf !globalConfig))
      end
    | "Config.append", args -> begin
        begin match !globalConfig with
        | None -> globalConfig := Some (Twelf.Config.read "sources.cfg")
        | _ -> ()
        end;
        serve (Twelf.Config.append (valOf !globalConfig))
      end
    | "make", args ->
        let fileName = getFile (args, "sources.cfg") in
        begin
          globalConfig := Some (Twelf.Config.read fileName);
          serve (Twelf.Config.load (valOf !globalConfig))
        end
    | "reset", args -> begin
        checkEmpty args;
        begin
          Twelf.reset ();
          serve Twelf.Ok
        end
      end
    | "loadFile", args -> serve (Twelf.loadFile (getFile' args))
    | "readDecl", args -> begin
        checkEmpty args;
        serve (Twelf.readDecl ())
      end
    | "decl", args -> serve (Twelf.decl (getId (tokenize args)))
    | "top", args -> begin
        checkEmpty args;
        begin
          Twelf.top ();
          serve Twelf.Ok
        end
      end
    | "Table.top", args -> begin
        checkEmpty args;
        begin
          Twelf.Table.top ();
          serve Twelf.Ok
        end
      end
    | "version", args -> begin
        print (Twelf.version ^ "\n");
        serve Twelf.Ok
      end
    | "help", args -> begin
        print helpString;
        serve Twelf.Ok
      end
    | t, args -> error ("Unrecognized command " ^ quote t)

  and serveLine () = serve' (readLine ())

  and serve = function
    | Twelf.Ok -> begin
        issue Twelf.Ok;
        serveLine ()
      end
    | Twelf.Abort -> begin
        issue Twelf.Abort;
        serveLine ()
      end

  let rec serveTop status =
    try serve status with
    | Error msg -> begin
        print (("Server error: " ^ msg) ^ "\n");
        serveTop Twelf.Abort
      end
    | exn -> begin
        print (("Uncaught exception: " ^ exnMessage exn) ^ "\n");
        serveTop Twelf.Abort
      end

  let rec server (name, _) =
    begin
      print (Twelf.version ^ "\n");
      begin
        Timing.init ();
        begin
          serveTop Twelf.Ok;
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
