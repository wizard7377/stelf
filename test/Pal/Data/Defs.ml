let def_basic_test =
  {|
%sort df_nat %.
%term df_zero df_nat %.
%term df_succ {_ df_nat} df_nat %.
%def df_one df_nat (df_succ df_zero)
%sort df_vec {_ df_nat} %.
%term df_nil df_vec df_zero %.
%term df_cons {n df_nat} {_ df_vec n} df_vec (df_succ n) %.
%term df_singleton df_vec df_one %.
|}

let def_inferred_test =
  {|
%sort di_nat %.
%term di_zero di_nat %.
%term di_succ {_ di_nat} di_nat %.
%def di_two _ (di_succ (di_succ di_zero))
%sort di_using {_ di_nat} %.
%term di_base di_using di_two %.
|}

let def_prop_test =
  {|
%sort dp_prop %.
%term dp_imp {_ dp_prop} {_ dp_prop} dp_prop %.
%term dp_false dp_prop %.
%def dp_neg ({_ dp_prop} dp_prop) ([p] dp_imp p dp_false)
%sort dp_pf {_ dp_prop} %.
%term dp_neg_elim {p dp_prop} {_ dp_pf p} {_ dp_pf (dp_neg p)} dp_pf dp_false %.
|}
