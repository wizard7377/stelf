let nats1 = {|
%sort nat
%term z nat
%term s {_ nat} nat
|}

let nats2 =
  {|

%sort even {_ nat}
%term even-z even z
%term even-s {{N}} %if (even (s (s N))) %<- (even N)

|}

let nats3 =
  {|
%sort plus {_ nat} {_ nat} {_ nat}
%term plus-z {{N2}} plus z N2 N2
%term plus-s {{N1 N2 N3}}
  %if (plus (s N1) N2 (s N3))
  %<- (plus N1 N2 N3)
|}
(* TODO Fix prec of arrows fix sort w/o names *)

let nats4 =
  {|
%mode plus %in %in %out
%worlds () (plus _ _ _)

%total N1 (plus N1 _ _)
|}
