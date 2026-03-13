(* # 1 "src/table/table_.sig.ml" *)
open! Basis

(* Hash Tables *)
(* Author: Frank Pfenning *)
(* Modified: Roberto Virga *)
(* This provides a common interface to hash tables *)
(* red/black trees and similar data structures *)
module type TABLE = sig
  type nonrec key

  (* parameter *)
  type nonrec 'a entry = key * 'a
  type nonrec 'a table_

  val new_ : int -> 'a table_

  (* size hint for some implementations *)
  val insert : 'a table_ -> 'a entry -> unit

  (* insert entry, return shadowed entry if there is one *)
  val insertShadow : 'a table_ -> 'a entry -> 'a entry option
  val lookup : 'a table_ -> key -> 'a option
  val delete : 'a table_ -> key -> unit
  val clear : 'a table_ -> unit

  (* Apply function to all entries in unpredictable order *)
  val app : ('a entry -> unit) -> 'a table_ -> unit
end
(* signature TABLE *)

(* # 1 "src/table/table_.fun.ml" *)

(* # 1 "src/table/table_.sml.ml" *)
(* Re-export Queue sig and module that would otherwise be shadowed by stdlib Queue *)
module type QUEUE = Queue.QUEUE

module Queue = Queue.Queue
