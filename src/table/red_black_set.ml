(* # 1 "src/table/red_black_set.sig.ml" *)

open Basis

(* Sets *)
(* Author: Brigitte Pientka *)
(* This provides a common interface to ordered sets *)
(* based on red/black trees *)
include Red_black_set_intf
(* signature RBSET *)

(* # 1 "src/table/red_black_set.fun.ml" *)

(* # 1 "src/table/red_black_set.sml.ml" *)

(* redblack-set.sml
 *
 * This code is based on Chris Okasaki's implementation of
 * red-black trees.  The linear-time tree construction code is
 * based on the paper ""Constructing red-black trees"" by Hinze,
 * and the delete function is based on the description in Cormen,
 * Leiserson, and Rivest.
 *
 * A red-black tree should satisfy the following two invariants:
 *
 *   Red Invariant: each red node has a black parent.
 *
 *   Black Condition: each path from the root to an empty node has the
 *     same number of black nodes (the tree's black height).
 *
 * The Red condition implies that the root is always black and the Black
 * condition implies that any node with only one child will be black and
 * its child will be a red leaf.
 *)
module RBSet : RBSET = struct
  type nonrec key = int
  type 'a entry = key * 'a

  type 'a dict =
    | Empty
    | Red of ('a entry * 'a dict * 'a dict)
    | Black of ('a entry * 'a dict * 'a dict)

  (* considered black *)
  type 'a set = Set of int * 'a dict

  exception Error of string

  type 'a ordSet = 'a set ref

  let isEmpty = function Set (_, Empty) -> true | Set (_, _) -> false
  let empty = Set (0, Empty)
  let compare = Int.compare

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
    let lookup (Set (_n, dict)) key =
      let rec lk = function
        | Empty -> None
        | Red (e, left, right) -> lk' (e, left, right)
        | Black (e, left, right) -> lk' (e, left, right)
      and lk' ((key1, datum1), left, right) =
        begin match compare (key, key1) with
        | Equal -> Some datum1
        | Less -> lk left
        | Greater -> lk right
        end
      in
      lk dict

    let last (Set (n, dict)) = (n, valOf (lookup (Set (n, dict)) n))

    let restore_right = function
      | Black (e, Red lt, Red ((_, Red _, _) as rt)) ->
          Red (e, Black lt, Black rt)
      | Black (e, Red lt, Red ((_, _, Red _) as rt)) ->
          Red (e, Black lt, Black rt)
      | Black (e, l, Red (re, Red (rle, rll, rlr), rr)) ->
          Black (rle, Red (e, l, rll), Red (re, rlr, rr))
      | Black (e, l, Red (re, rl, (Red _ as rr))) ->
          Black (re, Red (e, l, rl), rr)
      | dict -> dict

    let restore_left = function
      | Black (e, Red ((_, Red _, _) as lt), Red rt) ->
          Red (e, Black lt, Black rt)
      | Black (e, Red ((_, _, Red _) as lt), Red rt) ->
          Red (e, Black lt, Black rt)
      | Black (e, Red (le, (Red _ as ll), lr), r) ->
          Black (le, ll, Red (e, lr, r))
      | Black (e, Red (le, ll, Red (lre, lrl, lrr)), r) ->
          Black (lre, Red (le, ll, lrl), Red (e, lrr, r))
      | dict -> dict

    let insert (Set (n, dict), ((key, _datum) as entry)) =
      let nItems = ref n in
      let rec ins = function
        | Empty -> begin
            nItems := n + 1;
            Red (entry, Empty, Empty)
          end
        | Red (((key1, _datum1) as entry1), left, right) -> begin
            match compare (key, key1) with
            | Equal -> Red (entry1, left, right)
            | Less -> Red (entry1, ins left, right)
            | Greater -> Red (entry1, left, ins right)
          end
        | Black (((key1, _datum1) as entry1), left, right) -> begin
            match compare (key, key1) with
            | Equal -> Black (entry1, left, right)
            | Less -> restore_left (Black (entry1, ins left, right))
            | Greater -> restore_right (Black (entry1, left, ins right))
          end
      in
      let dict' =
        begin match ins dict with
        | Red ((_, Red _, _) as t) -> Black t
        | Red ((_, _, Red _) as t) -> Black t
        | dict -> dict
        end
      in
      Set (!nItems, dict')

    let rec insertList = function
      | s_, [] -> s_
      | s_, e :: list -> insertList (insert (s_, e), list)

    let insertLast (Set (n, dict), datum) =
      let (Set (n', dic')) = insert (Set (n, dict), (n + 1, datum)) in
      Set (n', dic')

    let insertShadow (Set (n, dict), ((key, _datum) as entry)) =
      let oldEntry = ref None in
      let rec ins = function
        | Empty -> Red (entry, Empty, Empty)
        | Red (((key1, _datum1) as entry1), left, right) -> begin
            match compare (key, key1) with
            | Equal -> begin
                oldEntry := Some entry1;
                Red (entry, left, right)
              end
            | Less -> Red (entry1, ins left, right)
            | Greater -> Red (entry1, left, ins right)
          end
        | Black (((key1, _datum1) as entry1), left, right) -> begin
            match compare (key, key1) with
            | Equal -> begin
                oldEntry := Some entry1;
                Black (entry, left, right)
              end
            | Less -> restore_left (Black (entry1, ins left, right))
            | Greater -> restore_right (Black (entry1, left, ins right))
          end
      in
      let dict', _oldEntry' =
        begin
          oldEntry := None;
          ( begin match ins dict with
            | Red ((_, Red _, _) as t) -> Black t
            | Red ((_, _, Red _) as t) -> Black t
            | dict -> dict
            end,
            !oldEntry )
        end
      in
      Set (n, dict')

    let app f (Set (_n, dict)) =
      let rec ap = function
        | Empty -> ()
        | Red (e, left, right) -> ap' (e, left, right)
        | Black (e, left, right) -> ap' (e, left, right)
      and ap' ((_, datum), left, right) =
        begin
          ap left;
          begin
            f datum;
            ap right
          end
        end
      in
      ap dict

    let update f (Set (n, dict)) =
      let rec upd = function
        | Empty -> Empty
        | Red (e, left, right) -> Red (upd' (e, left, right))
        | Black (e, left, right) -> Black (upd' (e, left, right))
      and upd' ((k, datum), left, right) =
        let left' = upd left in
        let datum' = f datum in
        let right' = upd right in
        ((k, datum'), left', right')
      in
      Set (n, upd dict)

    let forall (Set (_n, dict)) f =
      let rec ap = function
        | Empty -> ()
        | Red (e, left, right) -> ap' (e, left, right)
        | Black (e, left, right) -> ap' (e, left, right)
      and ap' (entry, left, right) =
        begin
          ap left;
          begin
            f entry;
            ap right
          end
        end
      in
      ap dict

    let existsOpt (Set (_n, dict)) f =
      let rec ap = function
        | Empty -> None
        | Red (e, left, right) -> ap' (e, left, right)
        | Black (e, left, right) -> ap' (e, left, right)
      and ap' ((k, d), left, right) =
        begin if f d then begin
          print "SUCCESS\n";
          Some k
        end
        else begin
          print "FAILED\n";
          begin match ap left with None -> ap right | Some res -> Some res
          end
        end
        end
      in
      ap dict

    let exists (Set (_n, dict)) f =
      let rec ap = function
        | Empty -> false
        | Red (e, left, right) -> ap' (e, left, right)
        | Black (e, left, right) -> ap' (e, left, right)
      and ap' (entry, left, right) =
        begin if f entry then true else ap left || ap right
        end
      in
      ap dict

    let setsize (Set (n, _)) = n

    let rec next = function
      | (Red (_, _, b) as t) :: rest -> (t, left (b, rest))
      | (Black (_, _, b) as t) :: rest -> (t, left (b, rest))
      | _ -> (Empty, [])

    and left = function
      | Empty, rest -> rest
      | (Red (_, a, _) as t), rest -> left (a, t :: rest)
      | (Black (_, a, _) as t), rest -> left (a, t :: rest)

    let start m = left (m, [])

    type 'a digit =
      | Zero
      | One of 'a entry * 'a dict * 'a digit
      | Two of 'a entry * 'a dict * 'a entry * 'a dict * 'a digit

    let addItem (a, l) =
      let rec incr = function
        | a, t, Zero -> One (a, t, Zero)
        | a1, t1, One (a2, t2, r) -> Two (a1, t1, a2, t2, r)
        | a1, t1, Two (a2, t2, a3, t3, r) ->
            One (a1, t1, incr (a2, Black (a3, t3, t2), r))
      in
      incr (a, Empty, l)

    let linkAll t =
      let rec link = function
        | t, Zero -> t
        | t1, One (a, t2, r) -> link (Black (a, t2, t1), r)
        | t, Two (a1, t1, a2, t2, r) -> link (Black (a1, Red (a2, t2, t1), t), r)
      in
      link (Empty, t)

    let getEntry = function Red (x, _, _) -> x | Black (x, _, _) -> x

    let union (Set (n1, s1), Set (n2, s2)) =
      let rec ins = function
        | (Empty, _), n, result -> (n, result)
        | (Red (x, _, _), r), n, result ->
            ins (next r, n + 1, addItem (x, result))
        | (Black (x, _, _), r), n, result ->
            ins (next r, n + 1, addItem (x, result))
      in
      let rec union' (t1, t2, n, result) =
        begin match (next t1, next t2) with
        | (Empty, _), (Empty, _) -> (n, result)
        | (Empty, _), t2 -> ins (t2, n, result)
        | t1, (Empty, _) -> ins (t1, n, result)
        | (tree1, r1), (tree2, r2) ->
            let ((x, _d1) as e1) = getEntry tree1 in
            let ((y, _d2) as e2) = getEntry tree2 in
            begin match compare (x, y) with
            | Less -> union' (r1, t2, n + 1, addItem (e1, result))
            | Equal -> union' (r1, r2, n + 1, addItem (e1, result))
            | Greater -> union' (t1, r2, n + 1, addItem (e2, result))
            end
        end
      in
      begin match s1 with
      | Empty -> Set (n2, s2)
      | _ -> begin
          match s2 with
          | Empty -> Set (n1, s1)
          | _ ->
              let n, result = union' (start s1, start s2, 0, Zero) in
              Set (n, linkAll result)
        end
      end

    let intersection (Set (_, s1), Set (_, s2)) =
      let rec intersect (t1, t2, n, result) =
        begin match (next t1, next t2) with
        | (Empty, _r), (_tree, _r') -> (n, result)
        | (_tree, _r), (Empty, _r') -> (n, result)
        | (tree1, r1), (tree2, r2) ->
            let ((x, _d1) as e1) = getEntry tree1 in
            let ((y, _d2) as _e2) = getEntry tree2 in
            begin match compare (x, y) with
            | Less -> intersect (r1, t2, n, result)
            | Equal -> intersect (r1, r2, n + 1, addItem (e1, result))
            | Greater -> intersect (t1, r2, n, result)
            end
        end
      in
      let n, result = intersect (start s1, start s2, 0, Zero) in
      Set (n, linkAll result)

    let difference (Set (_, s1), Set (_, s2)) =
      let rec ins = function
        | (Empty, _), n, result -> (n, result)
        | (Red (x, _, _), r), n, result ->
            ins (next r, n + 1, addItem (x, result))
        | (Black (x, _, _), r), n, result ->
            ins (next r, n + 1, addItem (x, result))
      in
      let rec diff (t1, t2, n, result) =
        begin match (next t1, next t2) with
        | (Empty, _), _ -> (n, result)
        | t1, (Empty, _) -> ins (t1, n, result)
        | (tree1, r1), (tree2, r2) ->
            let ((x, _d1) as e1) = getEntry tree1 in
            let (y, _d2) = getEntry tree2 in
            begin match compare (x, y) with
            | Less -> diff (r1, t2, n + 1, addItem (e1, result))
            | Equal -> diff (r1, r2, n, result)
            | Greater -> diff (t1, r2, n, result)
            end
        end
      in
      let n, result = diff (start s1, start s2, 0, Zero) in
      Set (n, linkAll result)

    let difference2 (Set (_, s1), Set (_, s2)) =
      let rec ins = function
        | (Empty, _), n, result -> (n, result)
        | (Red (x, _, _), r), n, result ->
            ins (next r, n + 1, addItem (x, result))
        | (Black (x, _, _), r), n, result ->
            ins (next r, n + 1, addItem (x, result))
      in
      let rec diff (t1, t2, (n1, result1), (n2, result2)) =
        begin match (next t1, next t2) with
        | (Empty, _), t2 -> ((n1, result1), ins (t2, n2, result2))
        | t1, (Empty, _) -> (ins (t1, n1, result1), (n2, result2))
        | (tree1, r1), (tree2, r2) ->
            let ((x, _d1) as e1) = getEntry tree1 in
            let ((y, _d2) as e2) = getEntry tree2 in
            begin match compare (x, y) with
            | Less ->
                diff (r1, t2, (n1 + 1, addItem (e1, result1)), (n2, result2))
            | Equal -> diff (r1, r2, (n1, result1), (n2, result2))
            | Greater ->
                diff (t1, r2, (n1, result1), (n2 + 1, addItem (e2, result2)))
            end
        end
      in
      let (n1, result1), (n2, result2) =
        diff (start s1, start s2, (0, Zero), (0, Zero))
      in
      (Set (n1, linkAll result1), Set (n2, linkAll result2))

    let diffMod f_ (Set (_, s1), Set (_, s2)) =
      let rec ins = function
        | (Empty, _), n, result -> (n, result)
        | (Red (x, _, _), r), n, result ->
            ins (next r, n + 1, addItem (x, result))
        | (Black (x, _, _), r), n, result ->
            ins (next r, n + 1, addItem (x, result))
      in
      let rec diff (t1, t2, (n1, result1), (n2, result2)) =
        begin match (next t1, next t2) with
        | (Empty, _), t2 -> ((n1, result1), ins (t2, n2, result2))
        | t1, (Empty, _) -> (ins (t1, n1, result1), (n2, result2))
        | (tree1, r1), (tree2, r2) ->
            let ((x, d1) as e1) = getEntry tree1 in
            let ((y, d2) as e2) = getEntry tree2 in
            begin match compare (x, y) with
            | Less ->
                diff (r1, t2, (n1 + 1, addItem (e1, result1)), (n2, result2))
            | Equal -> begin
                f_ d1 d2;
                diff (r1, r2, (n1, result1), (n2, result2))
              end
            | Greater ->
                diff (t1, r2, (n1, result1), (n2 + 1, addItem (e2, result2)))
            end
        end
      in
      let (n1, result1), (n2, result2) =
        diff (start s1, start s2, (0, Zero), (0, Zero))
      in
      (Set (n1, linkAll result1), Set (n2, linkAll result2))

    let splitSets f_ (Set (_, s1), Set (_, s2)) =
      let rec ins = function
        | (Empty, _), n, result -> (n, result)
        | (Red (x, _, _), r), n, result ->
            ins (next r, n + 1, addItem (x, result))
        | (Black (x, _, _), r), n, result ->
            ins (next r, n + 1, addItem (x, result))
      in
      let rec split
          ( t1,
            t2,
            ((n, result) as nr),
            ((n1, result1) as nr1),
            ((n2, result2) as nr2) ) =
        begin match (next t1, next t2) with
        | (Empty, _), t2 -> (nr, nr1, ins (t2, n2, result2))
        | t1, (Empty, _) -> (nr, ins (t1, n1, result1), nr2)
        | (tree1, r1), (tree2, r2) ->
            let ((x, d1) as e1) = getEntry tree1 in
            let ((y, d2) as e2) = getEntry tree2 in
            begin match compare (x, y) with
            | Less -> split (r1, t2, nr, (n1 + 1, addItem (e1, result1)), nr2)
            | Equal -> begin
                match f_ d1 d2 with
                | None ->
                    split
                      ( r1,
                        r2,
                        nr,
                        (n1 + 1, addItem (e1, result1)),
                        (n2 + 1, addItem (e2, result2)) )
                | Some d ->
                    split (r1, r2, (n + 1, addItem ((x, d), result)), nr1, nr2)
              end
            | Greater -> split (t1, r2, nr, nr1, (n2 + 1, addItem (e2, result2)))
            end
        end
      in
      let (n, r), (n1, r1), (n2, r2) =
        split (start s1, start s2, (0, Zero), (0, Zero), (0, Zero))
      in
      (Set (n, linkAll r), Set (n1, linkAll r1), Set (n2, linkAll r2))
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
  (*print (""Found "" ^ Int.toString key ^ "" already in set -- keep entry--do not overwrite\n"");*)
  (* print (""Found "" ^ Int.toString key ^ "" already in set -- keep entry--do not overwrite\n""); *)
  (* re-color *)
  (* re-color *)
  (* input: set sc
     output set s' *)
  (* : 'a entry option ref *)
  (* re-color *)
  (* re-color *)
  (* Remove an item.  Raises LibBase.NotFound if not found. *)
  (* bbZip propagates a black deficit up the tree until either the top
         * is reached, or the deficit can be covered.  It returns a boolean
         * that is true if there is still a deficit and the zipped tree.
         *)
  (* case 1L *)
  (* case 1L *)
  (* case 3L *)
  (* case 3L *)
  (* case 4L *)
  (* case 4L *)
  (* case 2L *)
  (* case 2L *)
  (* case 1R *)
  (* case 1R *)
  (* case 3R *)
  (* case 3R *)
  (* case 4R *)
  (* case 4R *)
  (* case 2R *)
  (* case 2R *)
  (* end case *)
  (* end case *)
  (* local *)
  (* does not apply f to all elements of S in order! *)
  (* support for constructing red-black trees in linear time from increasing
   * ordered sequences (based on a description by R. Hinze).  Note that the
   * elements in the digits are ordered with the largest on the left, whereas
   * the elements of the trees are ordered with the largest on the right.
   *)
  (* functions for walking the tree while keeping a stack of parents
   * to be visited.
   *)
  (* add an item that is guaranteed to be larger than any in l *)
  (* link the digits into a tree *)
  (* return the union of the two sets *)
  (* return the intersection of the two sets *)
  (* return the set difference  S1 - S2 
     if there are elements in S2 which do not appear in S1
     they are ignored !*)
  (* returns difference (d1, d2) where d1 
     contains all elements occurring in S1 but not in S2
     and d2 contains all elements occurring in S2 but not in S1
       *)
  (* S1 - S2 = R1 
      S2 - S1 = R2
      intersection (S1, S2) requires 
      for all (x, d1) in S1 
        and (x, d2) in S2, d1 ~ d2
    *)
  let new_ () = ref empty

  (* ignore size hint *)
  let copy s_ =
    let s'_ = new_ () in
    begin
      s'_ := !s_;
      s'_
    end

  let insert = function
    | set -> ( function entry -> set := insert (!set, entry))

  let insertLast = function
    | set -> ( function datum -> set := insertLast (!set, datum))

  let insertList = function
    | set -> ( function list -> set := insertList (!set, list))

  let insertShadow = function
    | set -> ( function entry -> set := insertShadow (!set, entry))

  let isEmpty ordSet = isEmpty !ordSet
  let last ordSet = last !ordSet
  let lookup ordSet key = lookup !ordSet key
  let clear ordSet = ordSet := empty
  let app_internal_ = app
  let app ordSet f = app_internal_ f !ordSet

  let update = function
    | ordSet -> (
        function
        | f -> begin
            ordSet := update f !ordSet;
            ordSet
          end)

  let forall ordSet f = forall !ordSet f
  let exists ordSet f = exists !ordSet f
  let existsOpt ordSet f = existsOpt !ordSet f
  let size s_ = setsize !s_

  let difference = function
    | set1 -> (
        function
        | set2 ->
            let set = new_ () in
            begin
              set := difference (!set1, !set2);
              set
            end)

  let difference2 = function
    | set1 -> (
        function
        | set2 ->
            let r1 = new_ () in
            let r2 = new_ () in
            let rset1, rset2 = difference2 (!set1, !set2) in
            begin
              r1 := rset1;
              begin
                r2 := rset2;
                (r1, r2)
              end
            end)

  let differenceModulo = function
    | set1 -> (
        function
        | set2 -> (
            function
            | f_ ->
                let r1 = new_ () in
                let r2 = new_ () in
                let rset1, rset2 = diffMod f_ (!set1, !set2) in
                begin
                  r1 := rset1;
                  begin
                    r2 := rset2;
                    (r1, r2)
                  end
                end))

  let splitSets = function
    | set1 -> (
        function
        | set2 -> (
            function
            | f_ ->
                let r1 = new_ () in
                let r2 = new_ () in
                let r = new_ () in
                let rset, rset1, rset2 = splitSets f_ (!set1, !set2) in
                begin
                  r := rset;
                  begin
                    r1 := rset1;
                    begin
                      r2 := rset2;
                      (r, r1, r2)
                    end
                  end
                end))

  let intersection = function
    | set1 -> (
        function
        | set2 ->
            let set = new_ () in
            begin
              set := intersection (!set1, !set2);
              set
            end)

  let union = function
    | set1 -> (
        function
        | set2 ->
            let set = new_ () in
            begin
              set := union (!set1, !set2);
              set
            end)
end
(* functor RedBlackSet *)
