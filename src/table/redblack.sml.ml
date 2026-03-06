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
    let clear = function 
                         | table -> table := Empty;;
    let App_ = function 
                        | f -> function 
                                        | table -> (App_ (f, ! table));;
    end;;
(* functor RedBlackTree *);;
module StringRedBlackTree = (RedBlackTree)(struct
                                             type nonrec key' = string;;
                                             let compare = String.compare;;
                                             end);;
module IntRedBlackTree = (RedBlackTree)(struct
                                          type nonrec key' = int;;
                                          let compare = Int.compare;;
                                          end);;