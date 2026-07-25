(* Natural numbers with equality and ordering.
   Ported from twelf/examples/tapl_ch13/nat.elf.
   Note: %mode, %terminates, %unique omitted (not supported or not needed).
   nat is re-declared here to keep this chunk self-contained.
*)
let tapl_nat_base = {|
%sort nat
%name nat N
%term z nat
%term s {_ nat} nat
|}

let tapl_nat_eq =
  {|
%sort nat_eq {_ nat} {_ nat}
%sort nat_neq {_ nat} {_ nat}
%sort nat_lt {_ nat} {_ nat}

%term neq_eq_refl {{N}} nat_eq N N

%term nat_neq_zs {{N}} nat_neq z (s N)
%term nat_neq_sz {{N}} nat_neq (s N) z
%term nat_neq_ss {{N1 N2}} %if (nat_neq (s N1) (s N2)) %<- (nat_neq N1 N2)

%term nat_lt_zs {{N}} nat_lt z (s N)
%term nat_lt_ss {{N1 N2}} %if (nat_lt (s N1) (s N2)) %<- (nat_lt N1 N2)
|}
