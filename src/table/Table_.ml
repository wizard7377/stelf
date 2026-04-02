(* # 1 "src/table/Table.sig.ml" *)

open Basis

(* Hash Tables *)
(* Author: Frank Pfenning *)
(* Modified: Roberto Virga *)
(* This provides a common interface to hash tables *)

(** red/black trees and similar data structures *)
include Table_intf
(* signature TABLE *)

(* # 1 "src/table/Table.fun.ml" *)

(* # 1 "src/table/Table.sml.ml" *)
(* Re-export Queue sig and module that would otherwise be shadowed by stdlib Queue *)
module type QUEUE = Queue.QUEUE

module Queue = Queue.Queue
