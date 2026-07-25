(* Simply-typed lambda-calculus: types, terms, typing, values, and small-step semantics.
   Ported from twelf/examples/small_step/lam.elf (syntax + typing + values + step only;
   preservation and progress proofs omitted — they use Twelf automation not in STELF).
   Infix operators: => (type arrow, left 5), @ (application, left 5),
                    is (typing, left 5), ~> (step, left 5).
*)
let small_step_lam_types =
  {|
%sort tp
%sort tm

%term => {_ tp} {_ tp} tp
%prec %left 5 =>
|}

let small_step_lam_terms =
  {|
%term @ {_ tm} {_ tm} tm
%prec %left 5 @
%term lam {_ tp} {_ {_ tm} tm} tm
|}

let small_step_lam_typing =
  {|
%sort is {_ tm} {_ tp}
%prec %left 5 is

%term is_@ {{E1 E2 T1 T2}} {_ E1 is (T1 => T2)} {_ E2 is T1} (E1 @ E2) is T2
%term is_lam {{E T1 T2}} {_ {x tm} {_ x is T1} (E x) is T2} (lam T1 E) is (T1 => T2)
|}

let small_step_lam_value =
  {|
%sort value {_ tm}
%term value_lam {{T E}} value (lam T E)
|}

let small_step_lam_step =
  {|
%sort ~> {_ tm} {_ tm}
%prec %left 5 ~>

%term ~>_@1 {{E1 E1' E2}} {_ E1 ~> E1'} (E1 @ E2) ~> (E1' @ E2)
%term ~>_@2 {{E1 E2 E2'}} {_ value E1} {_ E2 ~> E2'} (E1 @ E2) ~> (E1 @ E2')
%term ~>_@3 {{T E1 E2}} {_ value E2} ((lam T E1) @ E2) ~> (E1 E2)
|}
