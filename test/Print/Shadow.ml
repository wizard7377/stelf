open! Global
open! Global.Global_
open! Intsyn
open! Intsyn.Lambda_
open! Names
open! Names.Names_
open! Print
open! Print.Print_

(** Constants that are no longer reachable under their own name.

    A [%scope]'s components stop being bare-visible once the scope closes, so a
    term mentioning one has no bare spelling. [Names.constQid] reports that by
    decorating the name as [%c%] -- a note to the reader rather than syntax,
    which a printer that treats it as an identifier escapes into [%%%c%%%].

    The namespace is what makes such a name printable again: [%( s c )] resolves
    [c] as a member of [s] and ignores what the bare name means at the point of
    use, so the printed form both says what it means and reads back. *)

let corpus =
  [
    {| %data sh-nat %{
         %term sh-z sh-nat %.
         %term sh-s {_ sh-nat} sh-nat %.
         %def sh-one sh-nat (sh-s sh-z) %} |};
    (* Any following top-level command closes the %scope session, which is
       what makes the constructors unreachable by their bare names. *)
    {| %term sh-other sh-nat |};
  ]

let printed_def = "%def sh-one sh-nat %(sh-nat sh-s) %(sh-nat sh-z)"

(* The signature is process-wide state, so a fresh session is all that is
   needed to look the results up afterwards. *)
let install () =
  let module P = Pal.Pal.Start () in
  List.iter (fun cmd -> ignore (P.exec cmd : Pal.Reply.t list)) corpus

let show name =
  match Names.constLookup (Names.Qid ([ "sh-nat" ], name)) with
  | None -> Alcotest.failf "constant sh-nat.%s not found" name
  | Some cid -> Print.conDecToString (IntSyn.sgnLookup cid)

(* The reference must be qualified, and nothing may be spelled with the
   marker: [%%] can only reach the output by escaping, and never usefully. *)
let qualifies () =
  install ();
  let got = show "sh-one" in
  Alcotest.(check string) "out-of-scope reference" printed_def got

(* The property the qualification exists for: the printed form is accepted
   again, and denotes the same thing -- which shows up as printing the same
   way a second time. *)
let reinstalls () =
  install ();
  let printed = show "sh-one" in
  let module Q = Pal.Pal.Start () in
  List.iter (fun cmd -> ignore (Q.exec cmd : Pal.Reply.t list)) corpus;
  (match Q.exec printed with
  | (_ : Pal.Reply.t list) -> ()
  | exception e ->
      Alcotest.failf "%S does not install: %s" printed (Printexc.to_string e));
  match Names.constLookup (Names.Qid ([], "sh-one")) with
  | None -> Alcotest.fail "re-installed sh-one not found"
  | Some cid ->
      Alcotest.(check string)
        "re-printed" printed
        (Print.conDecToString (IntSyn.sgnLookup cid))

let cases () =
  [
    ( "Shadow",
      [
        Alcotest.test_case "out-of-scope reference qualifies" `Quick qualifies;
        Alcotest.test_case "qualified reference reinstalls" `Quick reinstalls;
      ] );
  ]
