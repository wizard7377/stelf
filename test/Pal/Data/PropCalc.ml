(* Propositional calculus: intuitionistic natural deduction
   Ported from twelf/examples/prop-calc/prop-calc.elf
   Note: %infix declarations omitted (Twelf `%infix` → STELF `%prec`)
   Combined into a single string to avoid cross-chunk scope issues.
*)
let prop_calc_types =
  {|
%sort o
%name o A
%term imp {_ o} {_ o} o
%prec %right 10 imp
%term and {_ o} {_ o} o
%prec %right 11 and
%term true o
|}

(* Hilbert axioms - all require o, imp, and, true in scope.
   Uses infix notation for imp since it is declared %prec %right 10 *)
let prop_calc_hilbert =
  {|
%. Provability (Hilbert-style)
%sort pf {_ o}
%name pf P
%term K {{A B}} pf (A imp (B imp A))
%term S {{A B C}} pf ((A imp (B imp C)) imp ((A imp B) imp (A imp C)))
%term ONE pf true
%term PAIR {{A B}} pf (A imp (B imp (A and B)))
%term LEFT {{A B}} pf ((A and B) imp A)
%term RIGHT {{A B}} pf ((A and B) imp B)
%term MP {{A B}} {_ pf (A imp B)} {_ pf A} pf B
|}

(* Natural deduction: require o, imp, and, true to be in scope.
   Uses infix notation for imp and and. *)
let prop_calc_nd =
  {|
%. Natural deduction
%sort nd {_ o}
%name nd D
%term trueI nd true
%term andI {{A B}} {_ nd A} {_ nd B} nd (A and B)
%term andEL {{A B}} {_ nd (A and B)} nd A
%term andER {{A B}} {_ nd (A and B)} nd B
%term impliesI {{A B}} {_ {_ nd A} nd B} nd (A imp B)
%term impliesE {{A B}} {_ nd (A imp B)} {_ nd A} nd B
|}
