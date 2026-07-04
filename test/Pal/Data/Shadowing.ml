(* Test strings for name shadowing and targeted error scenarios.
   Each value is designed to be run as a single exec call in its own test group
   so that partial state mutation from a failure does not affect other tests. *)

(* Declares shd_sort_nat twice: second declaration should raise Names_.Error "Shadowing: ..." *)
let shadow_sort_redecl =
  {|
%sort shd_sort_nat
%sort shd_sort_nat
|}

(* Declares shd_term_zero twice after its base type: second term should raise Shadowing *)
let shadow_term_redecl =
  {|
%sort shd_term_nat
%term shd_term_zero shd_term_nat
%term shd_term_zero shd_term_nat
|}

(* Parse error: %sort with no name — parser expects an identifier after %sort *)
let error_parse_sort_empty = {| %sort |}

(* Parse error: %term with no arguments *)
let error_parse_term_empty = {| %term |}

(* Recon error: sort argument references an undeclared type family.
   err_undeclared_base_xyz is lowercase so it must be a declared constant,
   but it has never been declared. Reconstruction fails with "undeclared". *)
let error_recon_undeclared =
  {| %sort err_rel {_ err_undeclared_base_xyz} |}
