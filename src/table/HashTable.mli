(* # 1 "src/table/HashTable.sig.ml" *)

(* # 1 "src/table/HashTable.fun.ml" *)

(* # 1 "src/table/HashTable.sml.ml" *)
open Basis
open Table_

(* Hash Table *)
(* Author: Frank Pfenning *)
(* Modified: Roberto Virga *)

module HashTable (HashTable__0 : sig
  type key'

  val hash : key' -> int
  val eq : key' * key' -> bool
end) : TABLE with type key = HashTable__0.key'
