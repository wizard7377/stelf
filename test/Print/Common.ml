open! Global
open! Global.Global_
open! Intsyn
open! Intsyn.Lambda_
open! Names
open! Names.Names_
open! Print
open! Print.Print_

(* Installs [cmds] through the real Pal pipeline, then renders the
   declaration named [name] (in the given qualifying scopes, outermost
   first) back to a string via [conDecToString], with [Global.printArrowSugar]
   set to [arrow_sugar] for the duration of the render. *)
let condec_string ~arrow_sugar (cmds : string list) (scopes, name) : string =
  let module P = Pal.Pal.Start () in
  List.iter (fun cmd -> ignore (P.exec cmd : Pal.Reply.t list)) cmds;
  let qid = Names.Qid (scopes, name) in
  Global.printArrowSugar := arrow_sugar;
  let result =
    match Names.constLookup qid with
    | None -> Alcotest.failf "constant %s not found after installing" name
    | Some cid -> Print.conDecToString (IntSyn.sgnLookup cid)
  in
  Global.printArrowSugar := false;
  result

let contains ~needle haystack =
  let nlen = String.length needle in
  let hlen = String.length haystack in
  let rec go i =
    i + nlen <= hlen && (String.sub haystack i nlen = needle || go (i + 1))
  in
  go 0

let check_contains printed needle =
  Alcotest.(check bool)
    (Printf.sprintf "contains %S" needle)
    true (contains ~needle printed)

let check_not_contains printed needle =
  Alcotest.(check bool)
    (Printf.sprintf "does not contain %S" needle)
    false (contains ~needle printed)

let test (name : string) (f : unit -> unit) :
    string * unit Alcotest.test_case list =
  (name, [ Alcotest.test_case name `Quick f ])
