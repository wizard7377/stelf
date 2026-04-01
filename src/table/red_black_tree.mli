(* # 1 "src/table/red_black_tree.sig.ml" *)

(* # 1 "src/table/red_black_tree.fun.ml" *)
open Basis
open Table_

(* Red/Black Trees *)
(* Author: Frank Pfenning *)

module RedBlackTree (RedBlackTree__0 : sig
  type key'

  val compare : key' * key' -> order
end) : TABLE with type key = RedBlackTree__0.key'
