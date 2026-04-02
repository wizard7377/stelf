(* # 1 "src/index/IndexSkolem.sig.ml" *)

(* # 1 "src/index/IndexSkolem.fun.ml" *)
open! Basis
open Queue

(* Indexing (Constants and Skolem constants) *)
(* Author: Carsten Schuermann *)
(* Modified: Frank Pfenning *)

module MakeIndexSkolem (IndexSkolem__0 : sig
  module Global : GLOBAL
  module Queue : QUEUE
end) : Index_.INDEX
