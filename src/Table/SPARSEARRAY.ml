(* # 1 "src/table/SparseArray.sig.ml" *)

open Basis

(* Sparse 1-Dimensional Arrays *)
(* Author: Roberto Virga *)

module type SPARSE_ARRAY = sig
  type 'a array

  val array : 'a -> 'a array
  val sub : 'a array * int -> 'a
  val update : 'a array * int * 'a -> unit
  val extract : 'a array * int * int -> 'a Vector.vector

  type 'a __0 = {
    src : 'a Vector.vector;
    si : int;
    len : int option;
    dst : 'a array;
    di : int;
  }

  val copyVec : 'a __0 -> unit
  val app : (int * 'a -> unit) -> 'a array * int * int -> unit
  val foldl : (int * 'a * 'b -> 'b) -> 'b -> 'a array * int * int -> 'b
  val foldr : (int * 'a * 'b -> 'b) -> 'b -> 'a array * int * int -> 'b
  val modify : (int * 'a -> 'a) -> 'a array * int * int -> unit
end
