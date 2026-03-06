# 1 "src/table/red_black_tree.sig.ml"

# 1 "src/table/red_black_tree.fun.ml"
open! Basis;;
(* Red/Black Trees *);;
(* Author: Frank Pfenning *);;
module RedBlackTree(RedBlackTree__0: sig
                                     type nonrec key'
                                     val compare : (key' * key') -> order
                                     end) : TABLE
  =
  struct
    type nonrec key = key';;
    type nonrec 'a entry = key * 'a;;
    type 'a dict =
      | Empty 
      | Red of 'a entry * 'a dict * 'a dict 
      | Black of 'a entry * 'a dict * 'a dict ;;
    (* considered black *);;
    type nonrec 'a table_ = 'a dict ref;;
    (* Representation Invariants *);;
    (*
     1. The tree is ordered: for every node Red((key1,datum1), left, right) or
        Black ((key1,datum1), left, right), every key in left is less than
        key1 and every key in right is greater than key1.

     2. The children of a red node are black (color invariant).

     3. Every path from the root to a leaf has the same number of
        black nodes, called the black height of the tree.
  *);;
    open!
      struct
        let rec lookup dict key =
          let rec lk =
            function 
                     | Empty -> None
                     | Red tree -> lk' tree
                     | Black tree -> lk' tree
          and lk' ((key1, datum1), left, right) =
            begin
            match compare (key, key1)
            with 
                 | Equal -> (Some datum1)
                 | LESS -> lk left
                 | GREATER -> lk right
            end in lk dict;;
        let rec restore_right =
          function 
                   | Black (e, Red lt, Red (((_, Red _, _) as rt)))
                       -> (Red (e, (Black lt), (Black rt)))
                   | Black (e, Red lt, Red (((_, _, Red _) as rt)))
                       -> (Red (e, (Black lt), (Black rt)))
                   | Black (e, l, Red (re, Red (rle, rll, rlr), rr))
                       -> (Black
                           (rle, (Red (e, l, rll)), (Red (re, rlr, rr))))
                   | Black (e, l, Red (re, rl, (Red _ as rr)))
                       -> (Black (re, (Red (e, l, rl)), rr))
                   | dict -> dict;;
        let rec restore_left =
          function 
                   | Black (e, Red (((_, Red _, _) as lt)), Red rt)
                       -> (Red (e, (Black lt), (Black rt)))
                   | Black (e, Red (((_, _, Red _) as lt)), Red rt)
                       -> (Red (e, (Black lt), (Black rt)))
                   | Black (e, Red (le, (Red _ as ll), lr), r)
                       -> (Black (le, ll, (Red (e, lr, r))))
                   | Black (e, Red (le, ll, Red (lre, lrl, lrr)), r)
                       -> (Black
                           (lre, (Red (le, ll, lrl)), (Red (e, lrr, r))))
                   | dict -> dict;;
        let rec insert (dict, ((key, datum) as entry)) =
          let rec ins =
            function 
                     | Empty -> (Red (entry, Empty, Empty))
                     | Red (((key1, datum1) as entry1), left, right)
                         -> begin
                            match compare (key, key1)
                            with 
                                 | Equal -> (Red (entry, left, right))
                                 | LESS -> (Red (entry1, ins left, right))
                                 | GREATER -> (Red (entry1, left, ins right))
                            end
                     | Black (((key1, datum1) as entry1), left, right)
                         -> begin
                            match compare (key, key1)
                            with 
                                 | Equal -> (Black (entry, left, right))
                                 | LESS
                                     -> restore_left
                                        ((Black (entry1, ins left, right)))
                                 | GREATER
                                     -> restore_right
                                        ((Black (entry1, left, ins right)))
                            end
            in begin
               match ins dict
               with 
                    | Red (((_, Red _, _) as t)) -> (Black t)
                    | Red (((_, _, Red _) as t)) -> (Black t)
                    | dict -> dict
               end;;
        open!
          struct
            exception NotFound ;;
            type 'a zipper =
              | Top 
              | Leftb of 'a entry * 'a dict * 'a zipper 
              | Leftr of 'a entry * 'a dict * 'a zipper 
              | Rightb of 'a dict * 'a entry * 'a zipper 
              | Rightr of 'a dict * 'a entry * 'a zipper ;;
            end;;
        let rec delete t key =
          let rec zip =
            function 
                     | (top_, t) -> t
                     | (Leftb (x, b, z), a) -> zip (z, (Black (x, a, b)))
                     | (Leftr (x, b, z), a) -> zip (z, (Red (x, a, b)))
                     | (Rightb (a, x, z), b) -> zip (z, (Black (x, a, b)))
                     | (Rightr (a, x, z), b) -> zip (z, (Red (x, a, b)))
            in let rec bbZip =
                 function 
                          | (top_, t) -> (true, t)
                          | (Leftb (x, Red (y, c, d), z), a)
                              -> bbZip (leftr_ (x, c, leftb_ (y, d, z)), a)
                          | (Leftb (x, Black (w, Red (y, c, d), e), z), a)
                              -> bbZip
                                 (leftb_
                                  (x, (Black (y, c, (Red (w, d, e)))), z), a)
                          | (Leftr (x, Black (w, Red (y, c, d), e), z), a)
                              -> bbZip
                                 (leftr_
                                  (x, (Black (y, c, (Red (w, d, e)))), z), a)
                          | (Leftb (x, Black (y, c, Red (w, d, e)), z), a)
                              -> (false,
                                  zip
                                  (z,
                                   (Black
                                    (y, (Black (x, a, c)), (Black (w, d, e))))))
                          | (Leftr (x, Black (y, c, Red (w, d, e)), z), a)
                              -> (false,
                                  zip
                                  (z,
                                   (Red
                                    (y, (Black (x, a, c)), (Black (w, d, e))))))
                          | (Leftr (x, Black (y, c, d), z), a)
                              -> (false,
                                  zip (z, (Black (x, a, (Red (y, c, d))))))
                          | (Leftb (x, Black (y, c, d), z), a)
                              -> bbZip (z, (Black (x, a, (Red (y, c, d)))))
                          | (Rightb (Red (y, c, d), x, z), b)
                              -> bbZip (rightr_ (d, x, rightb_ (c, y, z)), b)
                          | (Rightr (Red (y, c, d), x, z), b)
                              -> bbZip (rightr_ (d, x, rightb_ (c, y, z)), b)
                          | (Rightb (Black (y, Red (w, c, d), e), x, z), b)
                              -> bbZip
                                 (rightb_
                                  ((Black (w, c, (Red (y, d, e)))), x, z), b)
                          | (Rightr (Black (y, Red (w, c, d), e), x, z), b)
                              -> bbZip
                                 (rightr_
                                  ((Black (w, c, (Red (y, d, e)))), x, z), b)
                          | (Rightb (Black (y, c, Red (w, d, e)), x, z), b)
                              -> (false,
                                  zip
                                  (z,
                                   (Black
                                    (y, c, (Black (x, (Red (w, d, e)), b))))))
                          | (Rightr (Black (y, c, Red (w, d, e)), x, z), b)
                              -> (false,
                                  zip
                                  (z,
                                   (Red
                                    (y, c, (Black (w, (Red (w, d, e)), b))))))
                          | (Rightr (Black (y, c, d), x, z), b)
                              -> (false,
                                  zip (z, (Black (x, (Red (y, c, d)), b))))
                          | (Rightb (Black (y, c, d), x, z), b)
                              -> bbZip (z, (Black (x, (Red (y, c, d)), b)))
                          | (z, t) -> (false, zip (z, t))
                 in let rec delMin =
                      function 
                               | (Red (y, Empty, b), z)
                                   -> (y, (false, zip (z, b)))
                               | (Black (y, Empty, b), z)
                                   -> (y, bbZip (z, b))
                               | (Black (y, a, b), z)
                                   -> delMin (a, leftb_ (y, b, z))
                               | (Red (y, a, b), z)
                                   -> delMin (a, leftr_ (y, b, z))
                               | (Empty, _) -> raise Match
                      in let rec joinRed =
                           function 
                                    | (Empty, Empty, z) -> zip (z, Empty)
                                    | (a, b, z)
                                        -> let (x, (needB, b')) =
                                             delMin (b, top_) in begin
                                             if needB then
                                             (fun (_, r) -> r)
                                             (bbZip (z, (Red (x, a, b'))))
                                             else zip (z, (Red (x, a, b')))
                                             end
                           in let rec joinBlack =
                                function 
                                         | (a, Empty, z)
                                             -> (fun (_, r) -> r)
                                                (bbZip (z, a))
                                         | (Empty, b, z)
                                             -> (fun (_, r) -> r)
                                                (bbZip (z, b))
                                         | (a, b, z)
                                             -> let (x, (needB, b')) =
                                                  delMin (b, top_) in begin
                                                  if needB then
                                                  (fun (_, r) -> r)
                                                  (bbZip
                                                   (z, (Black (x, a, b'))))
                                                  else
                                                  zip (z, (Black (x, a, b')))
                                                  end
                                in let rec del =
                                     function 
                                              | (Empty, z) -> raise NotFound
                                              | (Black
                                                 (((key1, datum1) as entry1),
                                                  a, b),
                                                 z)
                                                  -> begin
                                                     match compare
                                                           (key, key1)
                                                     with 
                                                          | Equal
                                                              -> joinBlack
                                                                 (a, b, z)
                                                          | LESS
                                                              -> del
                                                                 (a,
                                                                  leftb_
                                                                  (entry1, b,
                                                                   z))
                                                          | GREATER
                                                              -> del
                                                                 (b,
                                                                  rightb_
                                                                  (a, entry1,
                                                                   z))
                                                     end
                                              | (Red
                                                 (((key1, datum1) as entry1),
                                                  a, b),
                                                 z)
                                                  -> begin
                                                     match compare
                                                           (key, key1)
                                                     with 
                                                          | Equal
                                                              -> joinRed
                                                                 (a, b, z)
                                                          | LESS
                                                              -> del
                                                                 (a,
                                                                  leftr_
                                                                  (entry1, b,
                                                                   z))
                                                          | GREATER
                                                              -> del
                                                                 (b,
                                                                  rightr_
                                                                  (a, entry1,
                                                                   z))
                                                     end
                                     in try begin
                                              del (t, top_);true
                                              end
                                        with 
                                             | NotFound -> false;;
        let rec insertShadow (dict, ((key, datum) as entry)) =
          let oldEntry = ref None
            in let rec ins =
                 function 
                          | Empty -> (Red (entry, Empty, Empty))
                          | Red (((key1, datum1) as entry1), left, right)
                              -> begin
                                 match compare (key, key1)
                                 with 
                                      | Equal
                                          -> begin
                                               oldEntry := ((Some entry1));
                                               (Red (entry, left, right))
                                               end
                                      | LESS
                                          -> (Red (entry1, ins left, right))
                                      | GREATER
                                          -> (Red (entry1, left, ins right))
                                 end
                          | Black (((key1, datum1) as entry1), left, right)
                              -> begin
                                 match compare (key, key1)
                                 with 
                                      | Equal
                                          -> begin
                                               oldEntry := ((Some entry1));
                                               (Black (entry, left, right))
                                               end
                                      | LESS
                                          -> restore_left
                                             ((Black
                                               (entry1, ins left, right)))
                                      | GREATER
                                          -> restore_right
                                             ((Black
                                               (entry1, left, ins right)))
                                 end
                 in begin
                      oldEntry := None;
                      (begin
                       match ins dict
                       with 
                            | Red (((_, Red _, _) as t)) -> (Black t)
                            | Red (((_, _, Red _) as t)) -> (Black t)
                            | dict -> dict
                       end, ! oldEntry)
                      
                      end;;
        let rec app f dict =
          let rec ap =
            function 
                     | Empty -> ()
                     | Red tree -> ap' tree
                     | Black tree -> ap' tree
          and ap' (entry1, left, right) =
            begin
              ap left;begin
                        f entry1;ap right
                        end
              end
            in ap dict;;
        end;;
    (* val restore_right : 'a dict -> 'a dict *);;
    (*
     restore_right (Black(e,l,r)) >=> dict
     where (1) Black(e,l,r) is ordered,
           (2) Black(e,l,r) has black height n,
           (3) color invariant may be violated at the root of r:
               one of its children might be red.
     and dict is a re-balanced red/black tree (satisfying all invariants)
     and same black height n.
  *);;
    (* re-color *);;
    (* re-color *);;
    (* l is black, deep rotate *);;
    (* l is black, shallow rotate *);;
    (* restore_left is like restore_right, except *);;
    (* the color invariant may be violated only at the root of left child *);;
    (* re-color *);;
    (* re-color *);;
    (* r is black, shallow rotate *);;
    (* r is black, deep rotate *);;
    (* val ins : 'a dict -> 'a dict  inserts entry *);;
    (* ins (Red _) may violate color invariant at root *);;
    (* ins (Black _) or ins (Empty) will be red/black tree *);;
    (* ins preserves black height *);;
    (* re-color *);;
    (* re-color *);;
    (* function below from .../smlnj-lib/Util/int-redblack-set.sml *);;
    (* Need to check and improve some time *);;
    (* Sun Mar 13 08:22:53 2005 -fp *);;
    (* Remove an item.  Returns true if old item found, false otherwise *);;
    (* bbZip propagates a black deficit up the tree until either the top
         * is reached, or the deficit can be covered.  It returns a boolean
         * that is true if there is still a deficit and the zipped tree.
         *);;
    (* case 1L *);;
    (* case 3L *);;
    (* case 3L *);;
    (* case 4L *);;
    (* case 4L *);;
    (* case 2L *);;
    (* case 2L *);;
    (* case 1R *);;
    (* case 1R *);;
    (* case 3R *);;
    (* case 3R *);;
    (* case 4R *);;
    (* case 4R *);;
    (* case 2R *);;
    (* case 2R *);;
    (* local *);;
    (* use non-imperative version? *);;
    (* : 'a entry option ref *);;
    (* re-color *);;
    (* re-color *);;
    let rec new_ n = ref Empty;;
    (* ignore size hint *);;
    let insert =
      function 
               | table
                   -> function 
                               | entry -> table := (insert (! table, entry));;
    let insertShadow =
      function 
               | table
                   -> function 
                               | entry
                                   -> let (dict, oldEntry) =
                                        insertShadow (! table, entry)
                                        in begin
                                             table := dict;oldEntry
                                             end;;
    let lookup = function 
                          | table -> function 
                                              | key -> lookup (! table) key;;
    let delete =
      function 
               | table -> function 
                                   | key -> begin
                                              delete (! table) key;()
                                              end;;
    let clear = function 
                         | table -> table := Empty;;
    let App_ = function 
                        | f -> function 
                                        | table -> (App_ (f, ! table));;
    end;;
(* functor RedBlackTree *);;
# 1 "src/table/red_black_tree.sml.ml"
