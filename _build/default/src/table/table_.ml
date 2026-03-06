# 1 "src/table/table_.sig.ml"
open! Basis;;
(* Hash Tables *);;
(* Author: Frank Pfenning *);;
(* Modified: Roberto Virga *);;
(* This provides a common interface to hash tables *);;
(* red/black trees and similar data structures *);;
module type TABLE = sig
                    type nonrec key
                    (* parameter *)
                    type nonrec 'a entry = key * 'a
                    type nonrec 'a table_
                    val new_ : int -> 'a table_
                    (* size hint for some implementations *)
                    val insert : 'a table_ -> 'a entry -> unit
                    (* insert entry, return shadowed entry if there is one *)
                    val
                      insertShadow : 'a table_ -> 'a entry -> 'a entry option
                    val lookup : 'a table_ -> key -> 'a option
                    val delete : 'a table_ -> key -> unit
                    val clear : 'a table_ -> unit
                    (* Apply function to all entries in unpredictable order *)
                    val app : ('a entry -> unit) -> 'a table_ -> unit
                    end;;
(* signature TABLE *);;
# 1 "src/table/table_.fun.ml"

# 1 "src/table/table_.sml.ml"
open! Basis;;
module StringHashTable = (HashTable)(struct
                                       type nonrec key' = string;;
                                       let hash = StringHash.stringHash;;
                                       let eq (x__op, y__op) = x__op = y__op;;
                                       end);;
module IntHashTable = (HashTable)(struct
                                    type nonrec key' = int;;
                                    let hash = function 
                                                        | n -> n;;
                                    let eq (x__op, y__op) = x__op = y__op;;
                                    end);;
module StringRedBlackTree = (RedBlackTree)(struct
                                             type nonrec key' = string;;
                                             let compare = String.compare;;
                                             end);;
module IntRedBlackTree = (RedBlackTree)(struct
                                          type nonrec key' = int;;
                                          let compare = Int.compare;;
                                          end);;
module SparseArray = (SparseArray)(struct
                                     module IntTable = IntHashTable;;
                                     end);;
module SparseArray2 = (SparseArray2)(struct
                                       module IntTable = IntHashTable;;
                                       end);;