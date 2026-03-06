open! Basis;;
module SigINT : SIGINT =
  struct
    let rec interruptLoop ((loop : unit -> unit)) =
      let origIntHandler =
        Signal.signal
        (Posix.Signal.int,
         (Signal.SIG_HANDLE
          (function 
                    | n
                        -> begin
                             print "\ninterrupt\n";
                             Process.interruptConsoleProcesses ()
                             end)))
        in loop ()
        (*
	val _ = print
""Upon interrupt at prompt => type\n\
\f to return to top-level of Twelf server\n\
\c to continue Twelf execution\n\
\q to quit the Twelf server\n""
        *);;
    end;;
(* structure SigINT *);;