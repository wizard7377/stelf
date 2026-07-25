let scope_open_test =
  {|
%sort sc_nat %.
%scope sc_nat %{
  %term sc_z sc_nat
  %term sc_s {_ sc_nat} sc_nat
%}
%open sc_nat
%sort sc_add {_ sc_nat} {_ sc_nat} {_ sc_nat} %.
%term sc_add_z {y sc_nat} sc_add sc_z y y %.
|}

let scope_qualified_test =
  {|
%sort sq_nat %.
%scope sq_nat %{
  %term sq_z sq_nat
  %term sq_s {_ sq_nat} sq_nat
%}
%sort sq_pair sq_nat sq_nat %.
%term sq_zz sq_pair %(sq_nat sq_z) %(sq_nat sq_z) %.
|}

let scope_open_inside_test =
  {|
%sort oi_bool %.
%scope oi_bool %{
  %term oi_true oi_bool
  %term oi_false oi_bool
%}
%scope oi_not %{
  %open oi_bool
  %sort oi_not oi_bool oi_bool
  %term oi_t oi_not oi_true oi_false
  %term oi_f oi_not oi_false oi_true
%}
|}

let local_basic_test =
  {|
%sort loc_nat %.
%scope loc_nat %{
  %term loc_z loc_nat
  %term loc_s {_ loc_nat} loc_nat
%}
%sort loc_pair {_ loc_nat} {_ loc_nat} %.
%term loc_pair_zz loc_pair (%local loc_nat loc_z) (%local loc_nat loc_z) %.
|}

let local_fallthrough_test =
  {|
%sort lo_nat %.
%scope lo_nat %{
  %term lo_z lo_nat
%}
%sort lo_rel {_ lo_nat} {_ lo_nat} %.
%term lo_base lo_nat %.
%term lo_use (%local lo_nat (lo_rel lo_z lo_base)) %.
|}
