(* # 1 "src/index/IndexSkolem.sig.ml" *)

(* # 1 "src/index/IndexSkolem.fun.ml" *)
open! Basis
open Queue

(* Indexing (Constants and Skolem constants) *)
(* Author: Carsten Schuermann *)
(* Modified: Frank Pfenning *)

module MakeIndexSkolem (Global : GLOBAL) (Queue : QUEUE) : Index_.INDEX
