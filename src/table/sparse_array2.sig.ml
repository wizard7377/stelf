open! Basis

(* Sparse 2-Dimensional Arrays *)
(* Author: Roberto Virga *)
module type SPARSE_ARRAY2 = sig
  type nonrec 'a array

  type nonrec 'a __0 = {
    base : 'a array;
    row : int;
    col : int;
    nrows : int;
    ncols : int;
  }

  type nonrec 'a region = 'a __0
  type traversal = RowMajor | ColMajor

  val array : 'a -> 'a array
  val sub : 'a array * int * int -> 'a
  val update : 'a array * int * int * 'a -> unit
  val row : 'a array * int * (int * int) -> 'a Vector.vector
  val column : 'a array * int * (int * int) -> 'a Vector.vector
  val app : traversal -> (int * int * 'a -> unit) -> 'a region -> unit
  val fold : traversal -> (int * int * 'a * 'b -> 'b) -> 'b -> 'a region -> 'b
  val modify : traversal -> (int * int * 'a -> 'a) -> 'a region -> unit
end
(* signature SPARSE_ARRAY2 *)
