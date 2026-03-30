open Basis

(** Time-bounded execution helpers. *)

(* time-limit.sml
 *
 * COPYRIGHT (c) 1993 by AT&T Bell Laboratories.  See COPYRIGHT file for details.
 * Modified: Brigitte Pientka
 *)
module TimeLimit : sig
  exception TimeOut

  val time_limit : Time.time option -> ('a -> 'b) -> 'a -> 'b
  (** Execute [f x] with an optional timeout budget. *)

  val timeLimit : Time.time option -> ('a -> 'b) -> 'a -> 'b
  (** Compatibility alias for {!time_limit}. *)
end = struct
  exception TimeOut

  let time_limit = function None -> fun f x -> f x | Some _t -> assert false
  let timeLimit = time_limit
  (* TODO deal with this some time *)
  (*
  let rec timeLimit arg__0 arg__1 arg__2 =
    begin match (arg__0, arg__1, arg__2) with
    | None, f, x -> f x
    | Some t, f, x ->
        let _ = print (("TIME LIMIT : " ^ Time.toString t) ^ "sec \n") in
        let setitimer = SMLofNJ.IntervalTimer.setIntTimer in
        let rec timerOn () = ignore (setitimer (Some t)) in
        let rec timerOff () = ignore (setitimer None) in
        let escapeCont =
          SMLofNJ.Cont.callcc (function k ->
              begin
                SMLofNJ.Cont.callcc (function k' -> SMLofNJ.Cont.throw k k');
                begin
                  timerOff ();
                  raise TimeOut
                end 
              end)
        in
        let rec handler _ = escapeCont in
        begin
          Signals.setHandler (Signals.sigALRM, Signals.HANDLER handler);
          begin
            timerOn ();
            let _ = timerOff () in
            try f x
            with ex ->
              begin
                timerOff ();
                raise ex
              end
          end
        end
    end
    *)
end
(* TimeLimit *)
