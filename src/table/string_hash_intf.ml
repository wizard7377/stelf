(* # 1 "src/table/string_hash.sig.ml" *)

open Basis

(* String Hash Table *)
(* Author: Frank Pfenning *)

module type STRING_HASH = sig
  val stringHash : string -> int
end
