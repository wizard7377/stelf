open! Global
open! Global.Global_
open! Intsyn
open! Intsyn.Lambda_
open! Names
open! Names.Names_
open! Print
open! Print.Print_

(** Exact rendering of a small signature, and re-installation of it.

    The arrow-sugar cases next door check one feature at a time; these check
    what the printer actually emits, end to end, for the shapes that occur in
    real code.

    Two assertions per corpus:

    - the rendering is exactly what is written below, so a resugaring change
      that alters spacing, parenthesisation or naming shows up as a diff rather
      than silently;
    - feeding the rendering back in installs the same declarations again, which
      is the property the whole split exists to make true.

    [STELF_SHOW_PRINT=1] prints what was produced instead of comparing, which is
    how the expectations below are refreshed. *)

let render (cmds : string list) (names : string list) : string list =
  let module P = Pal.Pal.Start () in
  List.iter (fun cmd -> ignore (P.exec cmd : Pal.Reply.t list)) cmds;
  List.map
    (fun name ->
      match Names.constLookup (Names.Qid ([], name)) with
      | None -> Alcotest.failf "constant %s not found after installing" name
      | Some cid -> Print.conDecToString (IntSyn.sgnLookup cid))
    names

let golden (suite : string) (cmds : string list)
    (expected : (string * string) list) : unit -> unit =
 fun () ->
  let got = render cmds (List.map fst expected) in
  if Sys.getenv_opt "STELF_SHOW_PRINT" <> None then
    List.iter2
      (fun (n, _) s -> Printf.printf "%s | %S -> %S\n" suite n s)
      expected got
  else
    List.iter2
      (fun (n, want) got ->
        Alcotest.(check string) (Printf.sprintf "%s: %s" suite n) want got)
      expected got

(* Render the whole corpus, then install the rendering into a fresh session.
   Declarations are re-read in the order they were declared, so each one's
   dependencies are already present when it arrives. *)
let reinstalls (cmds : string list) (names : string list) : unit -> unit =
 fun () ->
  let printed = render cmds names in
  let module P = Pal.Pal.Start () in
  List.iter2
    (fun name src ->
      match P.exec src with
      | (_ : Pal.Reply.t list) -> ()
      | exception e ->
          Alcotest.failf "%s printed as %S, which does not install: %s" name src
            (Printexc.to_string e))
    names printed

let nat_cmds =
  [
    {| %sort g-nat |};
    {| %term g-z g-nat |};
    {| %term g-s {_ g-nat} g-nat |};
    {| %sort g-add {_ g-nat} {_ g-nat} {_ g-nat} |};
    {| %term g-add/z {y g-nat} g-add g-z y y |};
    {| %def g-two g-nat (g-s (g-s g-z)) |};
  ]

let nat_names = [ "g-nat"; "g-z"; "g-s"; "g-add"; "g-add/z"; "g-two" ]

(* [i-refl]'s type variable is inferred, so its declaration carries one leading
   implicit binder, named by [decEName] rather than [decLUName]. *)
let implicit_cmds =
  [
    {| %sort i-nat |};
    {| %sort i-eq {_ i-nat} {_ i-nat} |};
    {| %term i-refl {X i-nat} i-eq X X |};
  ]

let implicit_names = [ "i-nat"; "i-eq"; "i-refl" ]

let cases () =
  [
    ( "Golden",
      [
        Alcotest.test_case "nat" `Quick
          (golden "nat" nat_cmds
             [
               ("g-nat", "%sort g-nat");
               ("g-z", "%term g-z g-nat");
               ("g-s", "%term g-s {_0 g-nat} g-nat");
               ("g-add", "%sort g-add {_0 g-nat} {_1 g-nat} {_2 g-nat}");
               ("g-add/z", "%term g-add/z {y g-nat} g-add g-z y y");
               ("g-two", "%def g-two g-nat g-s (g-s g-z)");
             ]);
        Alcotest.test_case "implicits" `Quick
          (golden "implicits" implicit_cmds
             [
               ("i-nat", "%sort i-nat");
               ("i-eq", "%sort i-eq {_0 i-nat} {_1 i-nat}");
               ("i-refl", "%term i-refl {X i-nat} i-eq X X");
             ]);
        Alcotest.test_case "nat reinstalls" `Quick
          (reinstalls nat_cmds nat_names);
        Alcotest.test_case "implicits reinstall" `Quick
          (reinstalls implicit_cmds implicit_names);
      ] );
  ]
