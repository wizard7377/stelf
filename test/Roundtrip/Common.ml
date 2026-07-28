(** parse -> pretty -> parse.

    The property under test is that pretty-printing produces text the modern
    parser reads back as the same tree. That is what makes the printer's
    parenthesisation rules checkable at all: they encode [Modern.parse_expr]'s
    grammar, and this is the only way to find out whether they encode it
    correctly.

    Two assertions per case, and the second matters as much as the first:

    - [norm t1 = norm t2] -- printing did not change the term;
    - [s' = pretty t2] -- printing is idempotent.

    Without idempotence a printer could emit a form that parses to something
    different but then re-prints stably, and the first assertion alone would not
    notice. *)

module M = Modern.Modern
module P = Pretty.Make_Pretty (M.Cst)

(* The parser's own fixity type, reached through [Modern] rather than through
   [Names] directly: [Make_Modern] is applied to a sealed [Names], so the two
   spellings are not interchangeable. *)
module FX = M.Names.Fixity

let parse (s : string) : M.Cst.term = M.debug_parser (M.parse_expr ()) s

(* Operator declarations for the fixity suite. [Modern.local_fixity] is a
   module-level table that nothing ever clears, so these names are chosen not
   to occur anywhere in the base corpus: once registered they stay registered
   for the rest of the process. *)
let ops : (string * FX.fixity) list =
  [
    ("op-l", FX.Infix (FX.Strength 5, FX.Left));
    ("op-r", FX.Infix (FX.Strength 5, FX.Right));
    ("op-hi", FX.Infix (FX.Strength 7, FX.Left));
    ("op-n", FX.Infix (FX.Strength 5, FX.None));
    ("op-pre", FX.Prefix (FX.Strength 6));
    ("op-post", FX.Postfix (FX.Strength 6));
  ]

let parse_with_ops (s : string) : M.Cst.term =
  M.debug_parser_with_ops ops (M.parse_expr ()) s

(* The printer's own view of those same declarations. Keeping this separate
   from [ops] is the point of the callback: the printer never consults the
   parser's table, or the signature, or any other global. *)
let env_with_ops : Pretty.env =
  let table =
    [
      ("op-l", Pretty.Fixity.Infix (5, Pretty.Fixity.Left));
      ("op-r", Pretty.Fixity.Infix (5, Pretty.Fixity.Right));
      ("op-hi", Pretty.Fixity.Infix (7, Pretty.Fixity.Left));
      ("op-n", Pretty.Fixity.Infix (5, Pretty.Fixity.Non));
      ("op-pre", Pretty.Fixity.Prefix 6);
      ("op-post", Pretty.Fixity.Postfix 6);
    ]
  in
  {
    Pretty.default with
    fixity =
      (fun (ns, name) ->
        if ns <> [] then Pretty.Fixity.Nonfix
        else
          Option.value (List.assoc_opt name table) ~default:Pretty.Fixity.Nonfix);
  }

(* The deprecated debug dump is exactly what a failure message wants: an
   unambiguous rendering of the tree, produced by something other than the
   printer under test. *)
let show (t : M.Cst.term) : string = (M.Cst.show_term [@alert "-deprecated"]) t

let roundtrip ?(env = Pretty.default) ?(parse = parse) (input : string) :
    unit -> unit =
 fun () ->
  let t1 = parse input in
  let s' = P.term_to_string env t1 in
  (* A passing round trip says the output re-parses, not that it is idiomatic.
     [STELF_SHOW_PRETTY=1] dumps every rendering so the layout itself can be
     reviewed. *)
  if Sys.getenv_opt "STELF_SHOW_PRETTY" <> None then
    Printf.printf "  %-34s ->  %s\n" input s';
  let t2 =
    try parse s'
    with e ->
      Alcotest.failf "printed %S from %S, which does not parse back: %s" s'
        input (Printexc.to_string e)
  in
  if not (Norm.equal t1 t2) then
    Alcotest.failf
      "round trip changed the term.@\n\
      \  input:    %s@\n\
      \  printed:  %s@\n\
      \  before:   %s@\n\
      \  after:    %s"
      input s'
      (show (Norm.term t1))
      (show (Norm.term t2));
  let s'' = P.term_to_string env t2 in
  if s' <> s'' then
    Alcotest.failf "printing is not idempotent.@\n  first:  %s@\n  second: %s"
      s' s''

let case ?env ?parse (name : string) (input : string) : unit Alcotest.test_case
    =
  Alcotest.test_case name `Quick (roundtrip ?env ?parse input)

let suite (name : string) (cases : unit Alcotest.test_case list) = (name, cases)
