# 1 "test/regression.sig.ml"

# 1 "test/regression.fun.ml"

# 1 "test/regression.sml.ml"
open! Basis

(* Quiet regression test *)
(* Does not call ""use"", exits when it is done: suitable for mlton or sml/nj *)
(* Author: Robert J. Simmons *)
module RegressionTest = struct
  type command =
    | Test of string
    | TestUnsafe of string

  let _ = Frontend.Frontend_.Twelf.chatter := 0

  let run_make ~unsafe file =
    let previous_unsafe = !(Frontend.Frontend_.Twelf.unsafe) in
    Frontend.Frontend_.Twelf.unsafe := unsafe;
    let stat =
      try Frontend.Frontend_.Twelf.make file
      with _ -> Frontend.Frontend_.Twelf.Abort
    in
    Frontend.Frontend_.Twelf.unsafe := previous_unsafe;
    stat

  let parse_command str =
    if String.isPrefix "#" str then None
    else if String.isPrefix "testUnsafe" str then
      Some (TestUnsafe (String.extract (str, 11, Some (String.size str - 12))))
    else if String.isPrefix "test" str then
      Some (Test (String.extract (str, 5, Some (String.size str - 6))))
    else None

  let fail_if_abort phase file = function
    | Frontend.Frontend_.Twelf.Ok -> ()
    | Frontend.Frontend_.Twelf.Abort ->
        Alcotest.fail (phase ^ " failed for " ^ file)

  let run_case cmd =
    let file, unsafe =
      match cmd with
      | Test file -> (file, false)
      | TestUnsafe file -> (file, true)
    in
    
    Frontend.Frontend_.Twelf.doubleCheck := false;
    fail_if_abort "check" file (run_make ~unsafe file);
    Frontend.Frontend_.Twelf.doubleCheck := true;
    fail_if_abort "double-check" file (run_make ~unsafe file)

  let test_case_of_command line_no cmd =
    let title =
      match cmd with
      | Test file -> "line " ^ Int.toString line_no ^ " test " ^ file
      | TestUnsafe file -> "line " ^ Int.toString line_no ^ " testUnsafe " ^ file
    in
    Alcotest.test_case title `Quick (fun () -> run_case cmd)

  let run ?(alcotest_argv = [| "regression.exe" |]) filename =
    let file = TextIO.openIn filename in
    let rec readfile line_no acc =
      begin match TextIO.inputLine file with
      | None -> begin
          TextIO.closeIn file;
          List.rev acc
        end
      | Some s ->
          let next_acc =
            match parse_command s with
            | None -> acc
            | Some cmd -> test_case_of_command line_no cmd :: acc
          in
          readfile (line_no + 1) next_acc
      end
    in
    let cases = readfile 1 [] in
    Alcotest.run ~argv:alcotest_argv "twelf regression" [ ("regression", cases) ]
  (* Ignore any non-standard line *)
end
(* local... *)
(* structure RegressionTest *)

# 1 "test/runquiet.sml.ml"
open! Basis

module Run = struct
  let argv = CommandLine.arguments ()
  let alcotest_argv = [| "regression.exe" |]

  let _ =
    RegressionTest.run ~alcotest_argv
      (List.nth (argv, List.length argv - 1))
end
