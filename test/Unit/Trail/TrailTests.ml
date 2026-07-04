module T = Trail.Trail_.Trail

(* The trail stores arbitrary undo actions; callers decide what an "action" is.
   Tests use (ref, old_value) pairs so unwind can restore the original value. *)

let test_log_unwind () =
  let tr : (int ref * int) T.trail = T.trail () in
  let x = ref 10 in
  T.mark tr;
  T.log (tr, (x, !x));
  x := 99;
  T.unwind (tr, fun (r, v) -> r := v);
  Alcotest.(check int) "unwind restores value" 10 !x

let test_multiple_logs_unwind () =
  let tr : (int ref * int) T.trail = T.trail () in
  let x = ref 1 in
  let y = ref 2 in
  T.mark tr;
  T.log (tr, (x, !x));
  T.log (tr, (y, !y));
  x := 100;
  y := 200;
  T.unwind (tr, fun (r, v) -> r := v);
  Alcotest.(check int) "unwind restores x" 1 !x;
  Alcotest.(check int) "unwind restores y" 2 !y

let test_nested_marks () =
  let tr : (int ref * int) T.trail = T.trail () in
  let x = ref 0 in
  let y = ref 0 in
  T.mark tr;
  T.log (tr, (x, !x));
  x := 1;
  T.mark tr;
  T.log (tr, (y, !y));
  y := 2;
  (* inner unwind: only y should be restored *)
  T.unwind (tr, fun (r, v) -> r := v);
  Alcotest.(check int) "inner unwind: x unchanged" 1 !x;
  Alcotest.(check int) "inner unwind: y restored" 0 !y;
  (* outer unwind: x should now be restored *)
  T.unwind (tr, fun (r, v) -> r := v);
  Alcotest.(check int) "outer unwind: x restored" 0 !x

let test_reset_clears_trail () =
  let tr : (int ref * int) T.trail = T.trail () in
  let x = ref 5 in
  T.mark tr;
  T.log (tr, (x, !x));
  x := 50;
  T.reset tr;
  (* after reset, unwind is a no-op (no mark to stop at, Nil immediately) *)
  T.unwind (tr, fun (r, v) -> r := v);
  Alcotest.(check int) "reset: x not restored (trail cleared)" 50 !x

let test_lifo_order () =
  (* unwind applies undo actions in reverse (LIFO) order *)
  let tr : int T.trail = T.trail () in
  let order = ref [] in
  T.mark tr;
  T.log (tr, 1);
  T.log (tr, 2);
  T.log (tr, 3);
  T.unwind (tr, fun n -> order := n :: !order);
  (* unwind calls undo in LIFO order: 3, 2, 1.
     Each call prepends n to order, so the final list is [1; 2; 3]. *)
  Alcotest.(check (list int)) "LIFO unwind order (prepended)" [1; 2; 3] !order

let test_no_log_unwind_is_noop () =
  let tr : int T.trail = T.trail () in
  let x = ref 42 in
  T.mark tr;
  (* no logs between mark and unwind *)
  T.unwind (tr, fun _ -> x := 0);
  Alcotest.(check int) "unwind with no logs is a no-op" 42 !x

let suites =
  [ ( "Trail"
    , [ Alcotest.test_case "log and unwind" `Quick test_log_unwind
      ; Alcotest.test_case "multiple logs unwound" `Quick test_multiple_logs_unwind
      ; Alcotest.test_case "nested marks" `Quick test_nested_marks
      ; Alcotest.test_case "reset clears trail" `Quick test_reset_clears_trail
      ; Alcotest.test_case "LIFO unwind order" `Quick test_lifo_order
      ; Alcotest.test_case "unwind with no logs is noop" `Quick test_no_log_unwind_is_noop
      ] )
  ]
