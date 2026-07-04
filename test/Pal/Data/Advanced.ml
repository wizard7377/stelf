let reduces_test = {|
%sort rd_nat %.
%term rd_zero rd_nat %.
%term rd_succ {_ rd_nat} rd_nat %.
%sort rd_sub {_ rd_nat} {_ rd_nat} {_ rd_nat} %.
%term rd_sub_z  {x rd_nat} rd_sub x rd_zero x %.
%term rd_sub_z2 {y rd_nat} rd_sub rd_zero y rd_zero %.
%term rd_sub_ss {x rd_nat} {y rd_nat} {z rd_nat} {_ rd_sub x y z}
      rd_sub (rd_succ x) (rd_succ y) z %.
%mode {%in x rd_nat} {%in y rd_nat} {%out z rd_nat} rd_sub x y z
%reduces <= Z X (rd_sub X Y Z)
|}

let union_test = {|
%sort un_nat %.
%term un_zero un_nat %.
%term un_succ {_ un_nat} un_nat %.
%sort un_rel {_ un_nat} {_ un_nat} %.
%term un_eq  {x un_nat} un_rel x x %.
%block un_eq_block {x un_nat} {_ un_rel x x}
%block un_zero_block {_ un_rel un_zero un_zero}
%union un_hyps (un_eq_block un_zero_block)
%mode {%in x un_nat} {%in y un_nat} un_rel x y
%worlds (un_hyps) (un_rel _ _)
|}

let unique_test = {|
%sort uq_unit %.
%term uq_star uq_unit %.
%sort uq_eq {_ uq_unit} {_ uq_unit} %.
%term uq_refl {x uq_unit} uq_eq x x %.
%mode {%in x uq_unit} {%in y uq_unit} uq_eq x y
%worlds () (uq_eq _ _)
%unique uq_eq
|}
