(* Ackermann function in unary arithmetic
   Ported from twelf/examples/arith/arith.elf
   Note: %compile and %query directives omitted (not supported)
*)
let arith_nat = {|
%sort nat
%name nat X
%term z nat
%term s {_ nat} nat
|}

let arith_nt =
  {|
%sort nt {_ nat}
%name nt N
%term nt-z nt z
%term nt-s {{X}} %if (nt (s X)) %<- (nt X)
|}

let arith_plus =
  {|
%sort plus {_ nat} {_ nat} {_ nat}
%name plus P
%term p-z {{Y}} plus z Y Y
%term p-s {{X Y Z}} %if (plus (s X) Y (s Z)) %<- (plus X Y Z)
|}

let arith_acker =
  {|
%sort acker {_ nat} {_ nat} {_ nat}
%mode acker %in %in %out
%term a-1 {{Y}} acker z Y (s Y)
%term a-2 {{X Z}} %if (acker (s X) z Z) %<- (acker X (s z) Z)
%term a-3 {{X Y Z Z'}} %if (acker (s X) (s Y) Z) %<- (acker (s X) Y Z') %<- (acker X Z' Z)
%worlds () (acker _ _ _)
|}
