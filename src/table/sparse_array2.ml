(* # 1 "src/table/sparse_array2.sig.ml" *)

open Basis

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
  type traversal = RowMajor | ColMajor [@@deriving eq, ord, show]

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

(* # 1 "src/table/sparse_array2.fun.ml" *)
open Table_

(* Sparse 2-Dimensional Arrays *)
(* Author: Roberto Virga *)
module SparseArray2 (SparseArray2__0 : sig
  module IntTable : TABLE with type key = int
end) : SPARSE_ARRAY2 = struct
  open SparseArray2__0

  type nonrec 'a __1 = { default : 'a; table : 'a IntTable.table }
  type nonrec 'a array = 'a __1

  type nonrec 'a __0 = {
    base : 'a array;
    row : int;
    col : int;
    nrows : int;
    ncols : int;
  }

  type nonrec 'a region = 'a __0
  type traversal = RowMajor | ColMajor [@@deriving eq, ord, show]

  let size = 29

  let fromInt code =
    let rec fromInt' r =
      let code' = (r + 1) * (r + 2) / 2 in
      begin if code < code' then
        let diff = code' - code - 1 in
        (diff, r - diff)
      else fromInt' (r + 1)
      end
    in
    fromInt' 0

  let toInt (m, n) =
    let sum = m + n in
    (sum * (sum + 1) / 2) + n

  let unsafeSub ({ table; default }, i, j) =
    begin match IntTable.lookup table (toInt (i, j)) with
    | None -> default
    | Some v -> v
    end

  let unsafeUpdate ({ table; default = _default }, i, j, v) =
    IntTable.insert table (toInt (i, j), v)

  let checkRegion { base = _base; row; col; nrows; ncols } =
    row >= 0 && col >= 0 && nrows >= 0 && ncols >= 0

  let array default = { default; table = IntTable.new_ size }

  let sub (array, i, j) =
    begin if i >= 0 && j >= 0 then unsafeSub (array, i, j)
    else raise General.Subscript
    end

  let update (array, i, j, v) =
    begin if i >= 0 && j >= 0 then unsafeUpdate (array, i, j, v)
    else raise General.Subscript
    end

  let row (array, i, (j, len)) =
    begin if i >= 0 && j >= 0 && len >= 0 then
      Vector.tabulate (len, function off -> unsafeSub (array, i, j + off))
    else raise General.Subscript
    end

  let column (array, j, (i, len)) =
    begin if j >= 0 && i >= 0 && len >= 0 then
      Vector.tabulate (len, function off -> unsafeSub (array, i + off, j))
    else raise General.Subscript
    end

  let app traversal f ({ base; row; col; nrows; ncols } as region) =
    begin if checkRegion region then
      let rmax = row + nrows in
      let cmax = col + ncols in
      let rec appR (row', col') =
        begin if row' < rmax then begin
          if col' < cmax then begin
            f (row', col', unsafeSub (base, row', col'));
            appR (row', col' + 1)
          end
          else appR (row' + 1, col)
        end
        else ()
        end
      in
      let rec appC (row', col') =
        begin if col' < cmax then begin
          if row' < rmax then begin
            f (row', col', unsafeSub (base, row', col'));
            appC (row' + 1, col')
          end
          else appC (row, col' + 1)
        end
        else ()
        end
      in
      begin match traversal with
      | RowMajor -> appR (row, col)
      | ColMajor -> appC (row, col)
      end
    else raise General.Subscript
    end

  let fold traversal f init ({ base; row; col; nrows; ncols } as region) =
    begin if checkRegion region then
      let rmax = row + nrows in
      let cmax = col + ncols in
      let rec foldR (row', col') =
        begin if row' < rmax then begin
          if col' < cmax then
            f (row', col', unsafeSub (base, row', col'), foldR (row', col' + 1))
          else foldR (row' + 1, col)
        end
        else init
        end
      in
      let rec foldC (row', col') =
        begin if col' < cmax then begin
          if row' < rmax then
            f (row', col', unsafeSub (base, row', col'), foldC (row' + 1, col'))
          else foldC (row, col' + 1)
        end
        else init
        end
      in
      begin match traversal with
      | RowMajor -> foldR (row, col)
      | ColMajor -> foldC (row, col)
      end
    else raise General.Subscript
    end

  let modify traversal f ({ base; row; col; nrows; ncols } as region) =
    begin if checkRegion region then
      let rmax = row + nrows in
      let cmax = col + ncols in
      let rec modifyR (row', col') =
        begin if row' < rmax then begin
          if col' < cmax then begin
            unsafeUpdate
              (base, row', col', f (row', col', unsafeSub (base, row', col')));
            modifyR (row', col' + 1)
          end
          else modifyR (row' + 1, col)
        end
        else ()
        end
      in
      let rec modifyC (row', col') =
        begin if col' < cmax then begin
          if row' < rmax then begin
            unsafeUpdate
              (base, row', col', f (row', col', unsafeSub (base, row', col')));
            modifyC (row' + 1, col')
          end
          else modifyC (row, col' + 1)
        end
        else ()
        end
      in
      begin match traversal with
      | RowMajor -> modifyR (row, col)
      | ColMajor -> modifyC (row, col)
      end
    else raise General.Subscript
    end
end
(* structure SparseArray2 *)

(* # 1 "src/table/sparse_array2.sml.ml" *)
