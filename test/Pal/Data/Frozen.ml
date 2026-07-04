let freeze_basic_test = {|
%sort fr_nat %.
%term fr_zero fr_nat %.
%term fr_succ {_ fr_nat} fr_nat %.
%freeze fr_nat
%sort fr_pair {_ fr_nat} {_ fr_nat} %.
%term fr_zz fr_pair fr_zero fr_zero %.
|}

let freeze_violation_test = {|
%sort frv_nat %.
%term frv_zero frv_nat %.
%freeze frv_nat
%term frv_succ {_ frv_nat} frv_nat %.
|}

let thaw_unsafe_test = {|
%sort frt_nat %.
%term frt_zero frt_nat %.
%freeze frt_nat
%thaw frt_nat
|}
