(* Natural deduction for intuitionistic logic (positive+negative fragment).
   Ported from twelf/examples/guide/nd.elf.
   Abbreviation definitions for not/noti/note handled as regular terms
   since STELF does not support Twelf abbreviation syntax.
   The %block/%worlds declarations are kept as-is.
*)
let guide_nd =
  {|
%sort i
%name i T
%sort o
%name o A
%term imp {_ o} {_ o} o
%prec %right 10 imp
%term and {_ o} {_ o} o
%prec %right 11 and
%term true o
%term or {_ o} {_ o} o
%prec %right 11 or
%term false o
%term forall {_ {_ i} o} o
%term exists {_ {_ i} o} o

%sort nd {_ o}
%name nd D

%term impi {{A B}} {_ {_ nd A} nd B} nd (A imp B)
%term impe {{A B}} {_ nd (A imp B)} {_ nd A} nd B
%term andi {{A B}} {_ nd A} {_ nd B} nd (A and B)
%term ande1 {{A B}} {_ nd (A and B)} nd A
%term ande2 {{A B}} {_ nd (A and B)} nd B
%term truei nd true
%term ori1 {{A B}} {_ nd A} nd (A or B)
%term ori2 {{A B}} {_ nd B} nd (A or B)
%term ore {{A B C}} {_ nd (A or B)} {_ {_ nd A} nd C} {_ {_ nd B} nd C} nd C
%term falsee {{C}} {_ nd false} nd C
%term foralli {{A}} {_ {x i} nd (A x)} nd (forall A)
%term foralle {{A}} {_ nd (forall A)} {T i} nd (A T)
%term existsi {{A}} {T i} {_ nd (A T)} nd (exists A)
%term existse {{A C}} {_ nd (exists A)} {_ {x i} {_ nd (A x)} nd C} nd C

%block nd_hyp [A o] {u nd A}
%block nd_parm {x i}
%worlds (nd_hyp nd_parm) (nd A)

%sort red {_ nd A} {_ nd A}
%term impred {{A B D E}} red (impe (impi D) E) (D E)
%term andred1 {{A B D E}} red (ande1 (andi D E)) D
%term andred2 {{A B D E}} red (ande2 (andi D E)) E
%term orred1 {{A B C D E1 E2}} red (ore (ori1 D) E1 E2) (E1 D)
%term orred2 {{A B C D E1 E2}} red (ore (ori2 D) E1 E2) (E2 D)
%term forallred {{A D T}} red (foralle (foralli D) T) (D T)
%term existsred {{A C T D E}} red (existse (existsi T D) E) (E T D)

%theorem
trivI exists {D {A o} nd (A imp A)} true

%prove 2 {} (trivI D)
|}
