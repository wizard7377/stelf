open Common

let positive_single_hop () =
  let printed =
    condec_string ~arrow_sugar:true
      [ {| %sort as1_nat |}; {| %term as1_f {_ as1_nat} as1_nat |} ]
      ([], "as1_f")
  in
  check_contains printed "%pi as1_nat %-> as1_nat"

let negative_named_binder () =
  let printed =
    condec_string ~arrow_sugar:true
      [ {| %sort as2_nat |}; {| %term as2_f {x as2_nat} as2_nat |} ]
      ([], "as2_f")
  in
  check_not_contains printed "%pi"

(* Directly construct a Pi whose binder is anonymous (no user name) but
   whose dependency tag says the variable DOES occur (I.Maybe, as produced
   by a real occurs-check finding an occurrence) -- this must never be
   rewritten to arrow-sugar, regardless of anonymity. *)
let negative_anonymous_but_dependent () =
  Global.printArrowSugar := true;
  let d_ = IntSyn.Dec (None, IntSyn.Uni IntSyn.Type) in
  let pi = IntSyn.Pi ((d_, IntSyn.Maybe), IntSyn.Uni IntSyn.Type) in
  let printed = Print.expToString (IntSyn.Null, pi) in
  Global.printArrowSugar := false;
  check_not_contains printed "%pi"

let multi_hop () =
  let printed =
    condec_string ~arrow_sugar:true
      [
        {| %sort as4_nat |};
        {| %term as4_f {_ as4_nat} {_ as4_nat} {_ as4_nat} as4_nat |};
      ]
      ([], "as4_f")
  in
  check_contains printed "%pi as4_nat %-> as4_nat %-> as4_nat %-> as4_nat";
  (* Exactly one %pi -- not re-prefixed per hop. *)
  Alcotest.(check int)
    "single %pi prefix" 1
    (String.split_on_char ' ' printed
    |> List.filter (fun tok -> tok = "%pi")
    |> List.length)

let flag_off_regression () =
  let printed =
    condec_string ~arrow_sugar:false
      [ {| %sort as5_nat |}; {| %term as5_f {_ as5_nat} as5_nat |} ]
      ([], "as5_f")
  in
  check_not_contains printed "%pi"

let cases () =
  Alcotest.run "Print" @@ Golden.cases ()
  @ [
      test "Pi arrow-sugar: single non-dependent hop" positive_single_hop;
      test "Pi arrow-sugar: named binder stays explicit" negative_named_binder;
      test "Pi arrow-sugar: anonymous but dependent stays explicit"
        negative_anonymous_but_dependent;
      test "Pi arrow-sugar: multi-hop collapses to one %pi" multi_hop;
      test "Pi arrow-sugar: flag off is a no-op" flag_off_regression;
    ]
