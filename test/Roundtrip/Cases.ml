open Common

let cases () =
  Alcotest.run "ROUNDTRIP" @@ Direct.cases ()
  @ [
      suite "Atoms"
        [
          case "variable" "nat";
          case "uppercase" "X";
          case "underscore-initial" "_X";
          case "omitted" "_";
          case "type universe" "%type";
          case "qualified" "%val ( a b )";
          case "qualified (abs)" "%abs ( a b )";
          case "qualified unary" "%val plus";
          case "local" "%(ns (f x))";
          case "text" "%[hello%]";
          case "text with percent" "%[100%% sure%]";
          case "text with closer" "%[[a %] b%]]";
          case "text empty" "%[%]";
        ];
      suite "Application"
        [
          case "simple" "succ zero";
          case "nested" "succ (succ zero)";
          case "three args" "add x y z";
          case "head is application" "(f x) y";
          case "arg is binder (trailing)" "f [x] x";
          case "arg is pi (trailing)" "f {x} x";
          case "binder is not last" "f ([x] x) y";
        ];
      suite "Binders"
        [
          case "lambda" "[x] x";
          case "lambda annotated" "[x nat] x";
          case "lambda multi-name" "[(x y) nat] x";
          case "lambda anonymous" "[_ nat] z";
          case "pi" "{x} x";
          case "pi annotated" "{x nat} x";
          case "pi multi-name" "{(x y) nat} x";
          case "nested" "{x nat} [y nat] f x y";
          (* A binder in the domain of a pi is a different tree from one in the
             body, and only the body position is a trail slot. *)
          case "binder in domain" "{x ([y] y)} x";
        ];
      suite "Arrows"
        [
          case "simple" "%pi a %-> b";
          case "chain" "%pi a %-> b %-> c";
          case "codomain is arrow" "%pi a %-> b %-> c %-> d";
          (* An arrow in domain position must be parenthesised: the chain is
             greedy, so an unparenthesised domain would absorb the rest. *)
          case "domain is arrow" "%pi (%pi a %-> b) %-> c";
          case "domain is pi" "%pi ({x nat} p x) %-> c";
          case "arrow under binder" "{x nat} %pi a %-> b";
          case "arrow as argument" "f (%pi a %-> b)";
          case "back arrow" "%pi a %<- b";
          case "back arrow chain" "%pi a %<- b %<- c";
        ];
      suite "Ascription"
        [
          case "simple" "%the nat zero";
          case "compound type" "%the (%pi a %-> b) f";
          (* [%the] has no trailing form, so it needs parentheses in every
             slot narrower than a full expression. *)
          case "as argument" "f (%the nat zero)";
          case "under binder" "[x nat] %the nat x";
          case "nested body" "%the nat (%the nat zero)";
        ];
      suite "Escaping"
        [
          case "space in name" "%val a%% b";
          case "paren in name" "%val a%%(b";
          case "brace in name" "%val a%%{b";
          case "bracket in name" "%val a%%[b";
          case "percent in name" "%val a%%%b";
          case "escaped keyword" "%%%type";
        ];
      suite "Operators"
        [
          case ~parse:parse_with_ops ~env:env_with_ops "infix" "a op-l b";
          case ~parse:parse_with_ops ~env:env_with_ops "left assoc"
            "a op-l b op-l c";
          case ~parse:parse_with_ops ~env:env_with_ops "right assoc"
            "a op-r b op-r c";
          case ~parse:parse_with_ops ~env:env_with_ops "mixed precedence"
            "a op-l b op-hi c";
          case ~parse:parse_with_ops ~env:env_with_ops "explicit grouping"
            "(a op-l b) op-hi c";
          case ~parse:parse_with_ops ~env:env_with_ops "non-associative"
            "a op-n b";
          case ~parse:parse_with_ops ~env:env_with_ops "prefix" "op-pre a";
          case ~parse:parse_with_ops ~env:env_with_ops "postfix" "a op-post";
          case ~parse:parse_with_ops ~env:env_with_ops "operand is application"
            "f x op-l g y";
          case ~parse:parse_with_ops ~env:env_with_ops "operand is binder"
            "a op-l [x] x";
          (* An operator name in operand position has to opt out of operator
             status, or it re-parses as the operator. *)
          case ~parse:parse_with_ops ~env:env_with_ops "operator as operand"
            "f (%val op-l)";
          case ~parse:parse_with_ops ~env:env_with_ops "operator applied bare"
            "%val op-l a b c";
        ];
    ]

let () = cases ()
