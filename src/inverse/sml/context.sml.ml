open! Basis

module Context : CONTEXT = struct
  module L = Lib

  type nonrec 'a ctx = 'a list

  exception Context of string

  let empty = []
  let rec lookup (l, n) = try Some (L.ith n l) with Fail _ -> None
  let rec push (ctx, p) = p :: ctx
  let rec list l = l
end
