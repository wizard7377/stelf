(* # 1 "src/heuristic/heuristic_.sig.ml" *)

(** Heuristic ordering and formatting utilities for search indices. *)

open Basis

(* Heuristics : Version 1.3 *)

(** Author: Carsten Schuermann *)

module type HEURISTIC = sig
  type nonrec __0 = {
    sd : int;
    ind : int option;
    c : int;
    m : int;
    r : int;
    p : int;
  }

  type nonrec index = __0

  val compare : index * index -> order
  (** Position (left to right) *)

  val index_to_string : index -> string
  (** Render an index as a diagnostic string. *)

  val indexToString : index -> string
  (** Compatibility alias for {!index_to_string}. *)
end
