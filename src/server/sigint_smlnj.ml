(* # 1 "src/server/sigint_smlnj.sig.ml" *)

(* # 1 "src/server/sigint_smlnj.fun.ml" *)

(* # 1 "src/server/sigint_smlnj.sml.ml" *)
open! Basis

module SigINT : Sigint.SIGINT = struct
  (* TODO *)
  (* let rec interruptLoop (loop : unit -> unit) =
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
    *)
  let rec interruptLoop (loop : unit -> unit) = loop ()
end
(* structure SigINT *)
