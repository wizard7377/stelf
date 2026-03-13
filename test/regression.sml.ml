open! Basis

(* Quiet regression test *)
(* Does not call ""use"", exits when it is done: suitable for mlton or sml/nj *)
(* Author: Robert J. Simmons *)
module RegressionTest = struct
  open! struct
    let _ = Frontend.Frontend_.Twelf.chatter := 0
    let errors = ref 0

    let rec reportError file =
      begin
        errors := !errors + 1;
        print (("Regression test failed on " ^ file) ^ "\n")
      end
  end

  let rec test file =
    let _ = print ("Test:        " ^ file) in
    let stat =
      try Frontend.Frontend_.Twelf.make file with _ -> Frontend.Frontend_.Twelf.Abort
    in
    begin match stat with
    | Frontend.Frontend_.Twelf.Ok -> Frontend.Frontend_.Twelf.Ok
    | Frontend.Frontend_.Twelf.Abort -> begin
        reportError file;
        Frontend.Frontend_.Twelf.Abort
      end
    end

  let rec testUnsafe file =
    let _ = print ("Test Unsafe: " ^ file) in
    let _ = Frontend.Frontend_.Twelf.unsafe := true in
    let stat =
      try Frontend.Frontend_.Twelf.make file with e -> Frontend.Frontend_.Twelf.Abort
    in
    let _ = Frontend.Frontend_.Twelf.unsafe := false in
    begin match stat with
    | Frontend.Frontend_.Twelf.Ok -> Frontend.Frontend_.Twelf.Ok
    | Frontend.Frontend_.Twelf.Abort -> begin
        reportError file;
        Frontend.Frontend_.Twelf.Abort
      end
    end

  let conclude : unit -> OS.Process.status = function
    | () ->
        let err = !errors in
        begin
          errors := 0;
          begin match err with
          | 0 -> begin
              print "Test complete with no errors\n";
              OS.Process.success
            end
          | 1 -> begin
              print "Test complete with 1 error\n";
              OS.Process.failure
            end
          | n -> begin
              print (("Test complete with " ^ Int.toString n) ^ " errors\n");
              OS.Process.failure
            end
          end
        end

  let rec process filename =
    let file = TextIO.openIn filename in
    let rec runline (str : string) =
      begin if String.isPrefix "#" str then None
      else begin
        if String.isPrefix "testUnsafe" str then
          Some
            (testUnsafe (String.extract (str, 11, Some (String.size str - 12))))
        else begin
          if String.isPrefix "test" str then
            Some (test (String.extract (str, 5, Some (String.size str - 6))))
          else None
        end
      end
      end
    in
    let exception Aborted in
    let rec getstatus (status, msg) =
      begin match status with
      | None -> ()
      | Some Frontend.Frontend_.Twelf.Ok -> print ("..." ^ msg)
      | Some Frontend.Frontend_.Twelf.Abort -> begin
          print "...ABORT!\n";
          raise Aborted
        end
      end
    in
    let rec readfile () =
      begin match TextIO.inputLine file with
      | None -> begin
          TextIO.closeIn file;
          conclude ()
        end
      | Some s -> (
          try
            begin
              Frontend.Frontend_.Twelf.doubleCheck := false;
              begin
                getstatus (runline s, "OK.\n");
                begin
                  Frontend.Frontend_.Twelf.doubleCheck := true;
                  begin
                    getstatus (runline s, "Double checked.\n");
                    readfile ()
                  end
                end
              end
            end
          with Aborted -> readfile ())
      end
    in
    readfile ()
  (* Ignore any non-standard line *)
end
(* local... *)
(* structure RegressionTest *)
