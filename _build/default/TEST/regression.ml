# 1 "TEST/regression.sig.ml"

# 1 "TEST/regression.fun.ml"

# 1 "TEST/regression.sml.ml"
open! Basis;;
(* Quiet regression test *);;
(* Does not call ""use"", exits when it is done: suitable for mlton or sml/nj *);;
(* Author: Robert J. Simmons *);;
module RegressionTest = struct
                          open!
                            struct
                              let _ = Twelf.chatter := 0;;
                              let errors = ref 0;;
                              let rec reportError file =
                                begin
                                  errors := ((! errors) + 1);
                                  print
                                  (("Regression test failed on " ^ file) ^
                                     "\n")
                                  
                                  end;;
                              end;;
                          let rec test file =
                            let _ = print ("Test:        " ^ file)
                              in let stat =
                                   try Twelf.make file
                                   with 
                                        | _ -> Twelf.abort_
                                   in begin
                                      match stat
                                      with 
                                           | ok_ -> Twelf.ok_
                                           | abort_
                                               -> begin
                                                    reportError file;
                                                    Twelf.abort_
                                                    end
                                      end;;
                          let rec testUnsafe file =
                            let _ = print ("Test Unsafe: " ^ file)
                              in let _ = Twelf.unsafe := true
                                   in let stat =
                                        try Twelf.make file
                                        with 
                                             | e -> Twelf.abort_
                                        in let _ = Twelf.unsafe := false
                                             in begin
                                                match stat
                                                with 
                                                     | ok_ -> Twelf.ok_
                                                     | abort_
                                                         -> begin
                                                              reportError
                                                              file;
                                                              Twelf.abort_
                                                              end
                                                end;;
                          let conclude : unit -> OS.Process.status =
                            function 
                                     | ()
                                         -> let err = ! errors
                                              in begin
                                                   errors := 0;
                                                   begin
                                                   match err
                                                   with 
                                                        | 0
                                                            -> begin
                                                                 print
                                                                 "Test complete with no errors\n";
                                                                 OS.Process.success
                                                                 
                                                                 end
                                                        | 1
                                                            -> begin
                                                                 print
                                                                 "Test complete with 1 error\n";
                                                                 OS.Process.failure
                                                                 
                                                                 end
                                                        | n
                                                            -> begin
                                                                 print
                                                                 (("Test complete with "
                                                                    ^
                                                                    (Int.toString
                                                                    n)) ^
                                                                    " errors\n");
                                                                 OS.Process.failure
                                                                 
                                                                 end
                                                   end
                                                   end;;
                          let rec process filename =
                            let file = TextIO.openIn filename
                              in let rec runline ((str : string)) = begin
                                   if String.isPrefix "#" str then None else
                                   begin
                                   if String.isPrefix "testUnsafe" str then
                                   (Some
                                    (testUnsafe
                                     (String.extract
                                      (str, 11,
                                       (Some ((String.size str) - 12))))))
                                   else begin
                                   if String.isPrefix "test" str then
                                   (Some
                                    (test
                                     (String.extract
                                      (str, 5,
                                       (Some ((String.size str) - 6))))))
                                   else None end end end
                                   in (let exception Aborted 
                                       in let rec getstatus (status, msg) =
                                            begin
                                            match status
                                            with 
                                                 | None -> ()
                                                 | Some ok_
                                                     -> print ("..." ^ msg)
                                                 | Some abort_
                                                     -> print
                                                        (begin
                                                           "...ABORT!\n";
                                                           raise Aborted
                                                           end)
                                            end
                                            in let rec readfile () =
                                                 begin
                                                 match TextIO.inputLine file
                                                 with 
                                                      | None
                                                          -> begin
                                                               TextIO.closeIn
                                                               file;
                                                               conclude ()
                                                               end
                                                      | Some s
                                                          -> try begin
                                                                   Twelf.doubleCheck
                                                                    := false;
                                                                   begin
                                                                    getstatus
                                                                    (runline
                                                                    s,
                                                                    "OK.\n");
                                                                    begin
                                                                    Twelf.doubleCheck
                                                                    := true;
                                                                    begin
                                                                    getstatus
                                                                    (runline
                                                                    s,
                                                                    "Double checked.\n");
                                                                    readfile
                                                                    ()
                                                                    end
                                                                    end
                                                                    end
                                                                   
                                                                   end
                                                             with 
                                                                  | Aborted
                                                                    -> 
                                                                    readfile
                                                                    ()
                                                 end in readfile ()
                                                 (* Ignore any non-standard line *));;
                          end;;
(* local... *);;
(* structure RegressionTest *);;