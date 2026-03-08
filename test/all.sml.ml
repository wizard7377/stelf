open! Basis;;

(* (Outdated) Regression test - *)
(* Author: Frank Pfenning *)
(* Twelf.chatter := 0; *)
(* Twelf.chatter := 1; *)
(* Twelf.chatter := 2; *)
(* Twelf.chatter := 5; *)
Twelf.doubleCheck := true;;

let rec test file =
  begin match Twelf.make file with ok_ -> Twelf.ok_ | abort_ -> raise Domain
  end

let rec testUnsafe file =
  let _ = Twelf.unsafe := true in
  let stat =
    try Twelf.make file
    with e ->
      begin
        Twelf.unsafe := false;
        raise e
      end
  in
  let _ = Twelf.unsafe := false in
  begin match stat with ok_ -> Twelf.ok_ | abort_ -> raise Domain
  end

let rec conclude () = ();;

use "TEST/regression.sml"
