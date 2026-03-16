(* # 1 "src/table/table.sig.ml" *)

open Basis

(* Hash Tables *)
(* Author: Frank Pfenning *)
(* Modified: Roberto Virga *)
(* This provides a common interface to hash tables *)

(** red/black trees and similar data structures *)
module type TABLE = sig
  type nonrec key

  type nonrec 'a entry = key * 'a
  (** parameter *)

  type nonrec 'a table

  val new_ : int -> 'a table

  val insert : 'a table -> 'a entry -> unit
  (** size hint for some implementations *)

  val insertShadow : 'a table -> 'a entry -> 'a entry option
  (** insert entry, return shadowed entry if there is one *)

  val lookup : 'a table -> key -> 'a option
  val delete : 'a table -> key -> unit
  val clear : 'a table -> unit

  val app : ('a entry -> unit) -> 'a table -> unit
  (** Apply function to all entries in unpredictable order *)
end
(* signature TABLE *)

(* # 1 "src/table/table.fun.ml" *)

(* # 1 "src/table/table.sml.ml" *)
(* Re-export Queue sig and module that would otherwise be shadowed by stdlib Queue *)
module type QUEUE = Queue.QUEUE

module Queue = Queue.Queue
