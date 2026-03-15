open! Basis

type make_result =
  | Ok
  | Abort
  | Exn of exn

let () = Printexc.record_backtrace true
let _ = Frontend.Frontend_.Twelf.chatter := 0

let run_make ~unsafe file =
  let previous_unsafe = !(Frontend.Frontend_.Twelf.unsafe) in
  Frontend.Frontend_.Twelf.unsafe := unsafe;
  let result =
    try
      match Frontend.Frontend_.Twelf.make file with
      | Frontend.Frontend_.Twelf.Ok -> Ok
      | Frontend.Frontend_.Twelf.Abort -> Abort
    with exn -> Exn exn
  in
  Frontend.Frontend_.Twelf.unsafe := previous_unsafe;
  result

let fail_if ?(should_fail = false) phase file = function
  | Ok -> ()
  | Abort ->
      if should_fail then ()
      else Alcotest.fail (phase ^ " failed for " ^ file ^ " (returned Abort)")
  | Exn exn ->
      let msg = Printf.sprintf "%s failed for %s (exception: %s\n%s)"
        phase file (Printexc.to_string exn) (Printexc.get_backtrace ())
      in
      if should_fail then ()
      else Alcotest.fail msg

let run_case ~unsafe ~success file =
  Frontend.Frontend_.Twelf.doubleCheck := false;
  fail_if ~should_fail:(not success) "check" file (run_make ~unsafe file);
  Frontend.Frontend_.Twelf.doubleCheck := true;
  fail_if ~should_fail:(not success) "double-check" file (run_make ~unsafe file)

let test ?(unsafe = false) ?(success = true) ?title file =
  let test_title =
    match title with
    | Some title -> title
    | None ->
        if unsafe then "testUnsafe " ^ file else "test " ^ file
  in
  Alcotest.test_case test_title `Quick (fun () -> run_case ~unsafe ~success file)
