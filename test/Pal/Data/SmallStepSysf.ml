(* SMALL-STEP-SYSTEM-F: system_f.elf (System F with nat)
   Ported from twelf/examples/small_step/system_f.elf.
   Operators: `=>` (left 5), `@` (left 5), `is` (left 5), `~>` (left 5), `#` (left 5).
   Dropped: preservation/progress proofs (use %block/%worlds unsupported forms).
   Note: `Lam` (capital L) = type abstraction; `#` = type application.
*)
let small_step_sysf_types =
  {|
%sort tp
%sort tm

%term nat tp
%term => {_ tp} {_ tp} tp
%prec %left 5 =>
%term forall {_ {_ tp} tp} tp
|}

let small_step_sysf_terms =
  {|
%term z tm
%term s {_ tm} tm
%term @ {_ tm} {_ tm} tm
%prec %left 5 @
%term lam {_ tp} {_ {_ tm} tm} tm
%term Lam {_ {_ tp} tm} tm
%term # {_ tm} {_ tp} tm
%prec %left 5 #
|}

let small_step_sysf_typing =
  {|
%sort is {_ tm} {_ tp}
%prec %left 5 is

%term is_z z is nat
%term is_s {{E}} {_ E is nat} (s E) is nat
%term is_@ {{E1 E2 T1 T2}} {_ E1 is (T1 => T2)} {_ E2 is T1} (E1 @ E2) is T2
%term is_lam {{E T1 T2}} {_ {x tm} {_ x is T1} (E x) is T2} (lam T1 E) is (T1 => T2)
%term is_Lam {{E T}} {_ {a tp} (E a) is (T a)} (Lam E) is (forall T)
%term is_# {{E T1 T2}} {_ E is (forall T1)} ((E # T2) is (T1 T2))
|}

let small_step_sysf_value =
  {|
%sort value {_ tm}
%term value_z value z
%term value_s {{V}} {_ value V} value (s V)
%term value_lam {{T E}} value (lam T E)
%term value_Lam {{E}} value (Lam E)
|}

let small_step_sysf_step =
  {|
%sort ~> {_ tm} {_ tm}
%prec %left 5 ~>

%term ~>_s {{E E'}} {_ E ~> E'} (s E) ~> (s E')
%term ~>_@1 {{E1 E1' E2}} {_ E1 ~> E1'} (E1 @ E2) ~> (E1' @ E2)
%term ~>_@2 {{E1 E2 E2'}} {_ value E1} {_ E2 ~> E2'} (E1 @ E2) ~> (E1 @ E2')
%term ~>_@3 {{T E1 E2}} {_ value E2} ((lam T E1) @ E2) ~> (E1 E2)
%term ~>_#1 {{E E' T}} {_ E ~> E'} (E # T) ~> (E' # T)
%term ~>_#2 {{E T}} (Lam E) # T ~> (E T)
|}

(* SMALL-STEP-SYSTEM-F-ISO: system_f_iso.elf (System F + iso-recursive types)
   Ported from twelf/examples/small_step/system_f_iso.elf.
   Adds: mu, roll, unroll, value_roll, ~>_roll, ~>_unroll1, ~>_unroll2.
   Dropped: preservation/progress proofs.
*)
let small_step_sysf_iso_types =
  {|
%sort tp
%sort tm

%term nat tp
%term => {_ tp} {_ tp} tp
%prec %left 5 =>
%term forall {_ {_ tp} tp} tp
%term mu {_ {_ tp} tp} tp
|}

let small_step_sysf_iso_terms =
  {|
%term z tm
%term s {_ tm} tm
%term @ {_ tm} {_ tm} tm
%prec %left 5 @
%term roll {_ tm} {_ tp} tm
%term unroll {_ tm} {_ tp} tm
%term lam {_ tp} {_ {_ tm} tm} tm
%term Lam {_ {_ tp} tm} tm
%term # {_ tm} {_ tp} tm
%prec %left 5 #
|}

let small_step_sysf_iso_typing =
  {|
%sort is {_ tm} {_ tp}
%prec %left 5 is

%term is_z z is nat
%term is_s {{E}} {_ E is nat} (s E) is nat
%term is_roll {{E T}} {_ E is (T (mu T))} (roll E (mu T)) is (mu T)
%term is_unroll {{E T}} {_ E is (mu T)} (unroll E (mu T)) is (T (mu T))
%term is_@ {{E1 E2 T1 T2}} {_ E1 is (T1 => T2)} {_ E2 is T1} (E1 @ E2) is T2
%term is_lam {{E T1 T2}} {_ {x tm} {_ x is T1} (E x) is T2} (lam T1 E) is (T1 => T2)
%term is_Lam {{E T}} {_ {a tp} (E a) is (T a)} (Lam E) is (forall T)
%term is_# {{E T1 T2}} {_ E is (forall T1)} ((E # T2) is (T1 T2))
|}

let small_step_sysf_iso_value =
  {|
%sort value {_ tm}
%term value_z value z
%term value_s {{V}} {_ value V} value (s V)
%term value_roll {{E T}} {_ value E} value (roll E T)
%term value_lam {{T E}} value (lam T E)
%term value_Lam {{E}} value (Lam E)
|}

let small_step_sysf_iso_step =
  {|
%sort ~> {_ tm} {_ tm}
%prec %left 5 ~>

%term ~>_s {{E E'}} {_ E ~> E'} (s E) ~> (s E')
%term ~>_@1 {{E1 E1' E2}} {_ E1 ~> E1'} (E1 @ E2) ~> (E1' @ E2)
%term ~>_@2 {{E1 E2 E2'}} {_ value E1} {_ E2 ~> E2'} (E1 @ E2) ~> (E1 @ E2')
%term ~>_@3 {{T E1 E2}} {_ value E2} ((lam T E1) @ E2) ~> (E1 E2)
%term ~>_#1 {{E E' T}} {_ E ~> E'} (E # T) ~> (E' # T)
%term ~>_#2 {{E T}} (Lam E) # T ~> (E T)
%term ~>_unroll1 {{E E' T}} {_ E ~> E'} (unroll E T) ~> (unroll E' T)
%term ~>_unroll2 {{E T1 T2}} {_ value E} (unroll (roll E T1) T2) ~> E
%term ~>_roll {{E E' T}} {_ E ~> E'} (roll E T) ~> (roll E' T)
|}
