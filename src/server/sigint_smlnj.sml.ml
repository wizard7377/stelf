open! Basis

module SigINT : SIGINT = struct
  let rec interruptLoop (loop : unit -> unit) =
    begin
      SMLofNJ.Cont.callcc (function k ->
          begin
            Signals.setHandler
              ( Signals.sigINT,
                Signals.HANDLER
                  (function
                  | _ -> begin
                      print "\ninterrupt\n";
                      k
                    end) );
            ()
          end);
      loop ()
    end
end
(* structure SigINT *)
