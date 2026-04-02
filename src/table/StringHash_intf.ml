(* # 1 "src/table/StringHash.sig.ml" *)

open Basis

(* String Hash Table *)
(* Author: Frank Pfenning *)

module type STRING_HASH = sig
  val stringHash : string -> int
end
