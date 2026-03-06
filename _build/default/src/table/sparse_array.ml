# 1 "src/table/sparse_array.sig.ml"
open! Basis;;
(* Sparse 1-Dimensional Arrays *);;
(* Author: Roberto Virga *);;
module type SPARSE_ARRAY = sig
                           type nonrec 'a array
                           val array : 'a -> 'a array
                           val sub : ('a array * int) -> 'a
                           val update : ('a array * int * 'a) -> unit
                           val
                             extract : ('a array * int * int) ->
                                       'a
                                       Vector.vector
                           type nonrec 'a __0 = { src: 'a Vector.vector ;
                             si: int ; len: int option ; dst: 'a array ;
                             di: int }
                           val copyVec : 'a __0 -> unit
                           val
                             app : ((int * 'a) -> unit) ->
                                   ('a array * int * int) ->
                                   unit
                           val
                             foldl : ((int * 'a * 'b) -> 'b) ->
                                     'b ->
                                     ('a array * int * int) ->
                                     'b
                           val
                             foldr : ((int * 'a * 'b) -> 'b) ->
                                     'b ->
                                     ('a array * int * int) ->
                                     'b
                           val
                             modify : ((int * 'a) -> 'a) ->
                                      ('a array * int * int) ->
                                      unit
                           end;;
(* signature SPARSE_ARRAY *);;
# 1 "src/table/sparse_array.fun.ml"
open! Basis;;
(* Sparse 1-Dimensional Arrays *);;
(* Author: Roberto Virga *);;
module SparseArray(SparseArray__0: sig module IntTable : TABLE end) : SPARSE_ARRAY
  =
  struct
    type nonrec 'a __0 = { default: 'a ; table: 'a IntTable.table_ };;
    type nonrec 'a array = 'a __0;;
    let size = 29;;
    let rec unsafeSub ({ table; default}, i) =
      begin
      match IntTable.lookup table i with 
                                         | None -> default
                                         | Some v -> v
      end;;
    let rec unsafeUpdate ({ table; default}, i, v) =
      IntTable.insert table (i, v);;
    let rec array default = { default; table = IntTable.new_ size} ;;
    let rec sub (array, i) = begin
      if i >= 0 then unsafeSub (array, i) else raise General.subscript_ end;;
    let rec update (array, i, v) = begin
      if i >= 0 then unsafeUpdate (array, i, v) else raise General.subscript_
      end;;
    let rec extract (array, i, len) = begin
      if (i >= 0) && (len >= 0) then
      Vector.tabulate (len, function 
                                     | off -> unsafeSub (array, i + off))
      else raise General.subscript_ end;;
    let rec copyVec { src; si; len; dst; di} = begin
      if di >= 0 then
      VectorSlice.appi
      (function 
                | (i, v) -> unsafeUpdate (dst, i, v))
      (VectorSlice.slice (src, si, len)) else raise General.subscript_ end;;
    let rec app f (array, i, len) = begin
      if (i >= 0) && (len >= 0) then
      let imax = i + len
        in let rec app' i' = begin
             if i' < imax then
             begin
               f (i', unsafeSub (array, i'));app' (i' + 1)
               end
             else () end in app' i
      else raise General.subscript_ end;;
    let rec foldl f init (array, i, len) = begin
      if (i >= 0) && (len >= 0) then
      let rec foldl' i' = begin
        if i' >= i then f (i', unsafeSub (array, i'), foldl' (i' - 1)) else
        init end in foldl' ((i + len) - 1)
      else raise General.subscript_ end;;
    let rec foldr f init (array, i, len) = begin
      if (i >= 0) && (len >= 0) then
      let imax = i + len
        in let rec foldr' i' = begin
             if i' < imax then f (i', unsafeSub (array, i'), foldr' (i' + 1))
             else init end in foldr' i
      else raise General.subscript_ end;;
    let rec modify f (array, i, len) = begin
      if (i >= 0) && (len >= 0) then
      let imax = i + len
        in let rec modify' i' = begin
             if i' < imax then
             begin
               unsafeUpdate (array, i', f (i', unsafeSub (array, i')));
               modify' (i' + 1)
               end
             else () end in modify' i
      else raise General.subscript_ end;;
    end;;
(* structure SparseArray *);;
# 1 "src/table/sparse_array.sml.ml"
