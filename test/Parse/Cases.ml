open Common

let nat_test =
  [ {| %sort nat |}; {| %term zero nat |}; {| %term succ {_ nat} nat |} ]

let add_test =
  [
    {| %sort add {_ nat} {_ nat} {_ nat} |};
    {| %term add/zero {y nat} add zero y y |};
    {| %term add/succ {x nat} {y nat} {z nat} {_ add x y z} add (succ x) y (succ z) |};
  ]

let mul_test =
  [
    {| %sort mul {_ nat} {_ nat} {_ nat} |};
    {| %term mul/zero {x nat} mul x zero zero |};
    {| %term mul/succ {x nat} {y nat} {z nat} {z' nat} {_ mul x y z} {_ add y z z'} (mul (succ x) y z') |};
  ]

let total_add_mul_test =
  [
    {| %mode {%in x nat} {%in y nat} {%out z nat} add x y z |};
    {| %worlds () (add _ _ _) |};
    {| %total N (add N _ _) |};
  ]

let cases () =
  Alcotest.run "Parse"
    begin
      [
        ( "Expressions",
          [
            test "Variables" Term "nat";
            test "Applications" Term "succ zero";
            test "Applications not small" ~failure:true Term1 "succ zero";
            test "Applications (nested)" Term "succ (succ zero)";
            test "Applications (nested, not small)" ~failure:true Term1
              "succ (succ zero)";
            test "Lambdas" Term "[x] x";
            test "Lambda (not small)" ~failure:true Term1 "[x] x";
            test "Pis" Term "{x} x";
            test "Pi (not small)" ~failure:true Term1 "{x} x";
            test "The" Term "%the nat zero";
            test "App (trailing)" Term "succ zero [x] x";
            test "Pi (trailing)" Term "f {x} x [y] y";
            test "Implicits" Term "_X";
            test "Qualified" Term "%val ( x y )";
            test "Nofix" Term "%val +";
            test "Qualified (abs)" Term "%abs ( x y )";
            test "Nofix (abs)" Term "%abs +";
            test "Abs unqualified" Term "%abs x";
            test "Local" Term "%local nat (ap F X)";
          ] );
        ( "Explicit implicits",
          [
            test "Simple" Term "{{X Y}} X Y";
            test "Nested" Term "{{X Y}} X {{Z}} Y Z";
          ] );
        ( "Hypotheses",
          [
            test "Simple" Decl "x nat";
            test "Multi" Decl "(x y) nat";
            test "Non-annotated" Decl "x";
            test "Non-annotated (multi)" Decl "(x y)";
            test "Unnamed" Decl "_ nat";
            test "Trash" Decl "_";
          ] );
        ( "Complex Expressions",
          [
            test "Declarations in lambda" Term "f [x nat] x";
            test "Multiple declarations in lambda" Term "f [(x y) nat] x";
            test "Nested lambda (body)" Term "f [x nat] [y nat] x";
            test "Nested lambda (binder)" Term "f [p {_ nat} nat] z";
            test "Declarations in Pi" Term "f {x nat} x";
            test "Multiple declarations in Pi" Term "f {(x y) nat} z";
            test "Nested pi (body)" Term "f {x nat} {y nat} x";
            test "Nested pi (binder)" Term "f {p {_ nat} nat} z";
            test "Lambda (large expression)" Term "f [x p zero] z";
            test "Pi (large expression)" Term "f {x p zero} z";
            test "Trailing (both sides)" Term "f y z [x nat] x y z";
          ] );
        ( "%sort",
          [
            test "Simple" Cmd1 "%sort nat";
            test "Simply indexed" Cmd1 "%sort prop {_ nat} {_ nat}";
            test "Simply indexed (multi)" Cmd1 "%sort prop {(x y) nat}";
            test "Complex" Cmd1 "%sort eq {t type} {x term t} {y term t}";
            test "Complex (multi)" Cmd1 "%sort eq {t type} {(x y) term t}";
            test "Complex (unnamed)" Cmd1
              "%sort eq {t type} {_ term t} {_ term t}";
            test "Complex (unnamed, multi)" Cmd1
              "%sort eq {t type} {(_ _) term t}";
            (* Parser accepts combined %sort; semantic handling not yet implemented *)
            test "Sorts (combined)" Cmd1 "%sort (nat bool)";
          ] );
        ( "%term",
          [
            test "Simple" Cmd1 "%term zero nat";
            test "Simply indexed" Cmd1
              "%term eq {t type} {x term t} {y term t} prop";
            test "Simply indexed (multi)" Cmd1
              "%term eq {t type} {(x y) term t} prop";
            test "Simply indexed (unnamed)" Cmd1
              "%term eq {t type} {_ term t} {_ term t} prop";
            test "Simply indexed (unnamed, multi)" Cmd1
              "%term eq {t type} {(_ _) term t} prop";
            test "Many terms" Cmd1 "%term (true false) bool";
          ] );
        ( "%def",
          [
            test "Simple" Cmd1 "%def not ({_ prop} prop) ([a] imp a false)";
            test "Simply indexed" Cmd1 "%def eq_i (pf (eq _A _A)) prop";
            test "Simply indexed (multi)" Cmd1
              "%def eq_i (pf (eq _A _A)) {(x y) prop} z";
            test "Simply indexed (unnamed)" Cmd1
              "%def _ (pf (eq _A _A)) {_ prop} z";
            test "Simply indexed (unnamed, multi)" Cmd1
              "%def eq_i (pf (eq _A _A)) {(_ _) prop} z";
          ] );
        ( "%mode",
          [
            test "Full" Cmd1
              "%mode {%in x nat} {%in y nat} {%out z nat} add x y z";
            test "Simple" Cmd1 "%mode add %in %in %out";
            test "Mixed" Cmd1 "%mode {%in x nat} {%in y nat} add x y %out";
          ] );
        ( "%block",
          [
            test "Simple" Cmd1 "%block test { x nat }";
            test "Multiple" Cmd1 "%block test { x nat } { y bool }";
            test "Some" Cmd1 "%block test [x nat]";
            test "Some (multi)" Cmd1 "%block test [(x y) nat]";
          ] );
        ( "%union",
          [
            test "Simple" Cmd1 "%union test (nat bool)";
            test "Many" Cmd1 "%union test (nat bool prop)";
          ] );
        ( "%worlds",
          [
            test "Simple" Cmd1 "%worlds () (add _ _ _)";
            test "Complex" Cmd1 "%worlds (N) (add N _ _)";
          ] );
        ( "%total",
          [
            test "Simple" Cmd1 "%total N (add N _ _)";
            test "Mutual" Cmd1 "%total (N1 N2) (add N1 _ _) (mul N2 _ _)";
          ] );
        ( "%terminates",
          [
            test "Simple" Cmd1 "%terminates N (add N _ _)";
            test "Mutual" Cmd1 "%terminates (N1 N2) (add N1 _ _) (mul N2 _ _)";
            test "Simultaneous" Cmd1 "%terminates [A B] max A B";
            test "Lexicographic" Cmd1 "%terminates {A B} max A B";
            test "Nested" Cmd1 "%terminates {A [B C] F} (max A (max B C))";
            test "Nested (mutual)" Cmd1
              "%terminates ({A [B C] G} [D E] F) (max A (max B C) max D (max E \
               C))";
            test "Nested (mutual)" Cmd1
              "%terminates ({A [B C]} [D E]) ((max A) (max B C) (max D (max E \
               C)))";
          ] );
        ( "%query",
          [
            test "Atomic (%?)" Cmd1 "%? nat";
            test "Complex (%?)" Cmd1 "%? add zero zero zero";
            test "Atom (Full)" Cmd1 "%query _ _ 1 add zero zero zero";
          ] );
        ( "%reduces",
          [
            test "Same size" Cmd1 "%reduces = X Y add X Y zero";
            test "Smaller" Cmd1 "%reduces < X Y add X Y zero";
            test "Larger" Cmd1 "%reduces > X Y add X Y zero";
            test "Same size or greater" Cmd1 "%reduces >= X Y add X Y zero";
            test "Same size or smaller" Cmd1 "%reduces <= X Y add X Y zero";
          ] );
        ("%prose", [ test "Basic" Cmd1 "%prose highlightHint" ]);
        ( "Parse errors",
          [
            (* %sort with no name: parser expects an identifier immediately after %sort *)
            test ~failure:true "sort: missing name" Cmd1 "%sort";
            (* %term with no arguments: expects name and type *)
            test ~failure:true "term: missing name and type" Cmd1 "%term";
            (* Unclosed brace in a binder *)
            test ~failure:true "unclosed brace" Term "{x nat";
            (* Unclosed paren *)
            test ~failure:true "unclosed paren" Term "(succ zero";
            (* Malformed sort name: open paren but no closing *)
            test ~failure:true "malformed sort arg" Cmd1 "%sort (nat";
          ] );
        ( "String literals",
          [
            test "Empty (single)" Term "%[%]";
            test "Simple (single)" Term "%[hello world%]";
            test "With percent (single)" Term "%[hello%world%]";
            test "As small expr (single)" Term1 "%[hello%]";
            test "Empty (double)" Term "%[[%]]";
            test "Simple (double)" Term "%[[hello world%]]";
            test "Embed single-close (double)" Term "%[[hello%]world%]]";
            test "Triple (exact close)" Term "%[[[a%]]]";
            test "Quadruple (exact close)" Term "%[[[[a%]]]]";
            test ~failure:true "Unclosed (single)" Term "%[hello";
            test ~failure:true "Unclosed (double)" Term "%[[hello%]";
            test ~failure:true "Bracket-only is unclosed" Term "%[]";
          ] );
        ( "Escapes and comments",
          [
            (* %%% is a literal % token; glued to `term` it is the identifier
               `%term`, NOT the keyword — so it parses as a plain term atom *)
            test "Escaped percent identifier" Term "%%%term";
            (* %%X escapes X into a literal identifier character *)
            test "Escaped char identifier" Term "%%!foo";
            (* `%term` (single %) is a command keyword, not a term atom *)
            test ~failure:true "Keyword is not a term atom" Term "%term";
            (* line comment `% ...` is skipped mid-term (inner context) *)
            test "Line comment between atoms" Term "succ % a comment\nzero";
            (* `%[ ... %]` in term position is a string value, not a comment *)
            test "String value in term" Term "%[hello%]";
          ] );
      ]
    end
    ~verbose:true
