open Basis

(** Time-bounded execution helpers. *)

(* time-limit.sml *)

module TimeLimit : sig
  exception TimeOut

  val time_limit : Time.time option -> ('a -> 'b) -> 'a -> 'b
  (** Execute [f x] with an optional timeout budget. *)

  val timeLimit : Time.time option -> ('a -> 'b) -> 'a -> 'b
  (** Compatibility alias for {!time_limit}. *)
end
