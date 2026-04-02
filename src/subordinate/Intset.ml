(* # 1 "src/subordinate/Intset.sig.ml" *)

(* # 1 "src/subordinate/Intset.fun.ml" *)

(* # 1 "src/subordinate/Intset.sml.ml" *)
open! Basis

(* Persistent red/black trees *)
(* Specialized for subordination *)
(* Author: Frank Pfenning *)
(* Copied from src/table/red-black-tree.fun *)
include Intset_intf
module IntSet : INTSET = struct
  type rbt = Empty | Red of (int * rbt * rbt) | Black of (int * rbt * rbt)

  (* considered black *)
  (* Representation Invariants *)
  (*
     1. The tree is ordered: for every node Red((key1,datum1), left, right) or
        Black ((key1,datum1), left, right), every key in left is less than
        key1 and every key in right is greater than key1.

     2. The children of a red node are black (color invariant).

     3. Every path from the root to a leaf has the same number of
        black nodes, called the black height of the tree.
  *)
  open! struct
    let rec lookup dict x =
      let rec lk = function
        | Empty -> false
        | Red (x1, left, right) -> lk' (x1, left, right)
        | Black (x1, left, right) -> lk' (x1, left, right)
      and lk' (x1, left, right) =
        begin match Int.compare (x, x1) with
        | Equal -> true
        | Less -> lk left
        | Greater -> lk right
        end
      in
      lk dict

    let rec restore_right = function
      | Black (e, Red lt, Red ((_, Red _, _) as rt)) ->
          Red (e, Black lt, Black rt)
      | Black (e, Red lt, Red ((_, _, Red _) as rt)) ->
          Red (e, Black lt, Black rt)
      | Black (e, l, Red (re, Red (rle, rll, rlr), rr)) ->
          Black (rle, Red (e, l, rll), Red (re, rlr, rr))
      | Black (e, l, Red (re, rl, (Red _ as rr))) ->
          Black (re, Red (e, l, rl), rr)
      | dict -> dict

    let rec restore_left = function
      | Black (e, Red ((_, Red _, _) as lt), Red rt) ->
          Red (e, Black lt, Black rt)
      | Black (e, Red ((_, _, Red _) as lt), Red rt) ->
          Red (e, Black lt, Black rt)
      | Black (e, Red (le, (Red _ as ll), lr), r) ->
          Black (le, ll, Red (e, lr, r))
      | Black (e, Red (le, ll, Red (lre, lrl, lrr)), r) ->
          Black (lre, Red (le, ll, lrl), Red (e, lrr, r))
      | dict -> dict

    let rec insert (dict, x) =
      let rec ins = function
        | Empty -> Red (x, Empty, Empty)
        | Red (x1, left, right) -> begin
            match Int.compare (x, x1) with
            | Equal -> Red (x, left, right)
            | Less -> Red (x1, ins left, right)
            | Greater -> Red (x1, left, ins right)
          end
        | Black (x1, left, right) -> begin
            match Int.compare (x, x1) with
            | Equal -> Black (x, left, right)
            | Less -> restore_left (Black (x1, ins left, right))
            | Greater -> restore_right (Black (x1, left, ins right))
          end
      in
      begin match ins dict with
      | Red ((_, Red _, _) as t) -> Black t
      | Red ((_, _, Red _) as t) -> Black t
      | dict -> dict
      end
  end

  (* val restore_right : 'a dict -> 'a dict *)
  (*
     restore_right (Black(e,l,r)) >=> dict
     where (1) Black(e,l,r) is ordered,
           (2) Black(e,l,r) has black height n,
	   (3) color invariant may be violated at the root of r:
               one of its children might be red.
     and dict is a re-balanced red/black tree (satisfying all invariants)
     and same black height n.
  *)
  (* re-color *)
  (* re-color *)
  (* l is black, deep rotate *)
  (* l is black, shallow rotate *)
  (* restore_left is like restore_right, except *)
  (* the color invariant may be violated only at the root of left child *)
  (* re-color *)
  (* re-color *)
  (* r is black, shallow rotate *)
  (* r is black, deep rotate *)
  (* val ins : 'a dict -> 'a dict  inserts entry *)
  (* ins (Red _) may violate color invariant at root *)
  (* ins (Black _) or ins (Empty) will be red/black tree *)
  (* ins preserves black height *)
  (* re-color *)
  (* re-color *)
  type nonrec intset = rbt

  let empty = Empty
  let insert (x, t) = insert (t, x)
  let member (x, t) = lookup t x

  let rec foldl f a t =
    let rec fo = function
      | Empty, r -> r
      | Red (x, left, right), r -> fo (right, f (x, fo (left, r)))
      | Black (x, left, right), r -> fo (right, f (x, fo (left, r)))
    in
    fo (t, a)
end
(* structure IntSet *)
