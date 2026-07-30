(** Round trips that start from a hand-built CST rather than from source.

    Some of the trees resugaring produces cannot be written down: an
    over-applied infix operator is one flat [App] node, but every source
    spelling of it parses to something else, and internal-tag nodes have no
    surface form at all. Those shapes still have to print, and print correctly,
    so they are built here directly. *)

module M = Modern.Modern
module C = M.Cst
module V = C.View
module T = V.Term
module P = Pretty.Make_Pretty (C)

let g : C.loc = V.Loc.review V.Loc.Ghost
let lc n = T.review (T.Lowercase (g, ([], n)))
let app f args = T.review (T.App (g, f, args))

let check ?(env = Pretty.default) (name : string) (build : unit -> C.term) :
    unit Alcotest.test_case =
  Alcotest.test_case name `Quick (fun () ->
      let t1 = build () in
      let s = P.term_to_string env t1 in
      let t2 =
        try M.debug_parser (M.parse_expr ()) s
        with e ->
          Alcotest.failf "printed %S, which does not parse back: %s" s
            (Printexc.to_string e)
      in
      (* Compared up to the rewrites the grammar forces -- see [Norm.denote].
         A hand-built tree can name a constant no source spelling reaches
         bare, so exact equality is the wrong bar here. *)
      if not (Norm.equal_denotation t1 t2) then
        Alcotest.failf
          "round trip changed the term.@\n\
          \  printed: %s@\n\
          \  before:  %s@\n\
          \  after:   %s"
          s
          (Common.show (Norm.denote t1))
          (Common.show (Norm.denote t2)))

(* Printing alone, for trees that are deliberately unparseable. The assertion
   is that the printer is total and produces the expected token. *)
let renders ?(env = Pretty.default) (name : string) (expected : string)
    (build : unit -> C.term) : unit Alcotest.test_case =
  Alcotest.test_case name `Quick (fun () ->
      Alcotest.(check string) name expected (P.term_to_string env (build ())))

let cases () =
  [
    Common.suite "Over-application"
      [
        (* [dropImp] can leave an infix constant with more arguments than its
           fixity takes. The flat node is what a round trip produces:
           [Modern.infix_op] builds [App (App (op, [a]), [b])] and
           [Term.view] n-arises that straight back into one [App]. *)
        check ~env:Common.env_with_ops "infix with three arguments" (fun () ->
            app (lc "op-l") [ lc "a"; lc "b"; lc "c" ]);
        check ~env:Common.env_with_ops "infix with one argument" (fun () ->
            app (lc "op-l") [ lc "a" ]);
        check ~env:Common.env_with_ops "prefix with two arguments" (fun () ->
            app (lc "op-pre") [ lc "a"; lc "b" ]);
        check ~env:Common.env_with_ops "postfix with two arguments" (fun () ->
            app (lc "op-post") [ lc "a"; lc "b" ]);
        check ~env:Common.env_with_ops "operator with no arguments" (fun () ->
            app (lc "op-l") []);
      ];
    Common.suite "Lexical class"
      [
        (* A constant whose name starts with a capital would re-parse as a
           variable if written bare, so it has to go through [%val]. *)
        check "uppercase-named constant" (fun () ->
            T.review (T.Lowercase (g, ([], "Nat"))));
        check "underscore-named constant" (fun () ->
            T.review (T.Lowercase (g, ([], "_nat"))));
        check "namespaced constant" (fun () ->
            T.review (T.Lowercase (g, ([ "ns" ], "nat"))));
        check "name containing a delimiter" (fun () ->
            T.review (T.Lowercase (g, ([], "a b"))));
        check "name that looks like a keyword" (fun () ->
            T.review (T.Lowercase (g, ([], "%term"))));
      ];
    Common.suite "Internal nodes"
      [
        renders "kind" "%%kind" (fun () ->
            T.review (T.Internal (g, C.Kind_tag, [])));
        renders "depth cutoff" "%%" (fun () ->
            T.review (T.Internal (g, C.Cutoff_tag, [])));
        renders "length cutoff" "..." (fun () ->
            T.review (T.Internal (g, C.Elided_tag, [])));
        renders "shift" "^3" (fun () ->
            T.review (T.Internal (g, C.Shift_tag 3, [])));
        renders "substitution" "(%%subst a b)" (fun () ->
            T.review (T.Internal (g, C.Subst_tag, [ lc "a"; lc "b" ])));
        renders "projection" "#lbl" (fun () ->
            T.review (T.Internal (g, C.Proj_tag "lbl", [])));
        (* [Foreign] is transparent: it prints as its child and so survives a
           round trip, unlike every other internal node. *)
        check "foreign is transparent" (fun () ->
            T.review (T.Foreign (g, app (lc "f") [ lc "x" ])));
        renders "internal inside an application" "f %%kind" (fun () ->
            app (lc "f") [ T.review (T.Internal (g, C.Kind_tag, [])) ]);
      ];
  ]
