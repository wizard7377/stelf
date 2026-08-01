module RBT = Table.TableInstances.IntRedBlackTree
module HT = Table.TableInstances.StringHashTable
module Q = Table.Queue.Queue
module R = Table.Ring.Ring

(* ── Red-Black Tree ──────────────────────────────── *)

let test_rbt_insert () =
  let t = RBT.new_ 4 in
  RBT.insert t (1, "a");
  Alcotest.(check (option string))
    "lookup after insert" (Some "a") (RBT.lookup t 1)

let test_rbt_missing () =
  let t = RBT.new_ 4 in
  Alcotest.(check (option string)) "lookup missing" None (RBT.lookup t 42)

let test_rbt_delete () =
  let t = RBT.new_ 4 in
  RBT.insert t (1, "a");
  RBT.delete t 1;
  Alcotest.(check (option string)) "lookup after delete" None (RBT.lookup t 1)

let test_rbt_shadow () =
  let t = RBT.new_ 4 in
  RBT.insert t (1, "a");
  let shadowed = RBT.insertShadow t (1, "b") in
  Alcotest.(check (option (pair int string)))
    "shadowed entry returned"
    (Some (1, "a"))
    shadowed;
  Alcotest.(check (option string))
    "new value stored" (Some "b") (RBT.lookup t 1)

let test_rbt_app_count () =
  let t = RBT.new_ 8 in
  List.iter (fun i -> RBT.insert t (i, i)) [ 1; 2; 3; 5; 7 ];
  let count = ref 0 in
  RBT.app (fun _ -> incr count) t;
  Alcotest.(check int) "app visits all 5 entries" 5 !count

let test_rbt_sorted_order () =
  let t = RBT.new_ 8 in
  List.iter (fun i -> RBT.insert t (i, i)) [ 3; 1; 4; 1; 5; 9; 2; 6 ];
  let keys = ref [] in
  RBT.app (fun (k, _) -> keys := k :: !keys) t;
  let sorted = List.sort compare !keys in
  Alcotest.(check bool)
    "app collects each inserted key" true
    (sorted = List.sort_uniq compare sorted)

let test_rbt_clear () =
  let t = RBT.new_ 4 in
  RBT.insert t (1, "x");
  RBT.clear t;
  Alcotest.(check (option string)) "clear empties table" None (RBT.lookup t 1)

(* ── Hash Table ──────────────────────────────────── *)

let test_ht_basic () =
  let t = HT.new_ 8 in
  HT.insert t ("foo", 42);
  Alcotest.(check (option int))
    "lookup after insert" (Some 42) (HT.lookup t "foo")

let test_ht_missing () =
  let t = HT.new_ 8 in
  Alcotest.(check (option int)) "lookup missing key" None (HT.lookup t "bar")

let test_ht_delete () =
  let t = HT.new_ 8 in
  HT.insert t ("foo", 1);
  HT.delete t "foo";
  Alcotest.(check (option int)) "lookup after delete" None (HT.lookup t "foo")

let test_ht_shadow () =
  let t = HT.new_ 8 in
  HT.insert t ("k", 1);
  let shadowed = HT.insertShadow t ("k", 2) in
  Alcotest.(check (option (pair string int)))
    "insertShadow returns old binding"
    (Some ("k", 1))
    shadowed;
  Alcotest.(check (option int)) "new value stored" (Some 2) (HT.lookup t "k")

let test_ht_clear () =
  let t = HT.new_ 8 in
  HT.insert t ("a", 1);
  HT.insert t ("b", 2);
  HT.clear t;
  let count = ref 0 in
  HT.app (fun _ -> incr count) t;
  Alcotest.(check int) "clear empties table" 0 !count

(* ── Queue ───────────────────────────────────────── *)

let test_queue_empty () =
  Alcotest.(check bool)
    "delete on empty returns None" true
    (Q.delete Q.empty = None)

let test_queue_fifo () =
  let q = Q.insert 1 (Q.insert 2 (Q.insert 3 Q.empty)) in
  (* insert prepends, so insertion order reversed: delete order is 3, 2, 1 *)
  match Q.delete q with
  | None -> Alcotest.fail "queue unexpectedly empty"
  | Some (x1, q') -> (
      match Q.delete q' with
      | None -> Alcotest.fail "queue unexpectedly empty"
      | Some (x2, q'') -> (
          match Q.delete q'' with
          | None -> Alcotest.fail "queue unexpectedly empty"
          | Some (x3, _) ->
              (* insert (a, insert (b, insert (c, empty))) → delete gives c, b, a *)
              Alcotest.(check (list int))
                "FIFO order" [ 3; 2; 1 ] [ x1; x2; x3 ]))

let test_queue_insert_front () =
  let q = Q.insert 2 Q.empty in
  let q = Q.insertFront 1 q in
  match Q.delete q with
  | None -> Alcotest.fail "queue unexpectedly empty"
  | Some (x, _) -> Alcotest.(check int) "insertFront element dequeued first" 1 x

let test_queue_to_list () =
  let q = Q.insert 1 (Q.insert 2 Q.empty) in
  let l, _ = Q.toList q in
  Alcotest.(check bool) "toList produces non-empty list" true (l <> [])

(* ── Ring ────────────────────────────────────────── *)

let test_ring_current () =
  let r = R.init [ 10; 20; 30 ] in
  Alcotest.(check int) "current is first element" 10 (R.current r)

let test_ring_next_advances () =
  let r = R.init [ 1; 2; 3 ] in
  Alcotest.(check int)
    "next advances to second element" 2
    (R.current (R.next r))

let test_ring_full_cycle () =
  let r = R.init [ 1; 2; 3 ] in
  let r3 = R.next (R.next (R.next r)) in
  Alcotest.(check int) "three nexts returns to start" 1 (R.current r3)

let test_ring_previous () =
  let r = R.init [ 1; 2; 3 ] in
  (* going back from 1 should wrap to 3 *)
  Alcotest.(check int)
    "previous from first wraps to last" 3
    (R.current (R.previous r))

let test_ring_foldr () =
  let r = R.init [ 1; 2; 3; 4; 5 ] in
  let sum = R.foldr (fun (x, acc) -> x + acc) 0 r in
  Alcotest.(check int) "foldr sums all elements" 15 sum

let test_ring_empty () =
  let r = R.init [] in
  Alcotest.(check bool) "empty ring" true (R.empty r)

let test_ring_insert () =
  let r = R.init [ 1; 2 ] in
  let r' = R.insert r 0 in
  let sum = R.foldr (fun (x, acc) -> x + acc) 0 r' in
  Alcotest.(check int) "insert adds element (sum now includes 0)" 3 sum

(* ── Suites ──────────────────────────────────────── *)

let rbt_suite =
  ( "RedBlackTree",
    [
      Alcotest.test_case "insert and lookup" `Quick test_rbt_insert;
      Alcotest.test_case "lookup missing key" `Quick test_rbt_missing;
      Alcotest.test_case "delete removes entry" `Quick test_rbt_delete;
      Alcotest.test_case "insertShadow returns old binding" `Quick
        test_rbt_shadow;
      Alcotest.test_case "app visits all entries" `Quick test_rbt_app_count;
      Alcotest.test_case "keys are unique after inserts" `Quick
        test_rbt_sorted_order;
      Alcotest.test_case "clear empties table" `Quick test_rbt_clear;
    ] )

let ht_suite =
  ( "HashTable",
    [
      Alcotest.test_case "basic insert and lookup" `Quick test_ht_basic;
      Alcotest.test_case "lookup missing key" `Quick test_ht_missing;
      Alcotest.test_case "delete removes entry" `Quick test_ht_delete;
      Alcotest.test_case "insertShadow returns old binding" `Quick
        test_ht_shadow;
      Alcotest.test_case "clear empties table" `Quick test_ht_clear;
    ] )

let queue_suite =
  ( "Queue",
    [
      Alcotest.test_case "delete on empty" `Quick test_queue_empty;
      Alcotest.test_case "FIFO ordering" `Quick test_queue_fifo;
      Alcotest.test_case "insertFront priority" `Quick test_queue_insert_front;
      Alcotest.test_case "toList non-empty" `Quick test_queue_to_list;
    ] )

let ring_suite =
  ( "Ring",
    [
      Alcotest.test_case "current element" `Quick test_ring_current;
      Alcotest.test_case "next advances" `Quick test_ring_next_advances;
      Alcotest.test_case "full cycle" `Quick test_ring_full_cycle;
      Alcotest.test_case "previous wraps" `Quick test_ring_previous;
      Alcotest.test_case "foldr sums all" `Quick test_ring_foldr;
      Alcotest.test_case "empty ring" `Quick test_ring_empty;
      Alcotest.test_case "insert grows ring" `Quick test_ring_insert;
    ] )

let suites = [ rbt_suite; ht_suite; queue_suite; ring_suite ]
