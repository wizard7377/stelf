(* Formula syntax for predicate calculus (intuitionistic and classical).
   Ported from twelf/examples/cut_elim/formulas.elf.
*)
let cut_elim_formulas =
  {|
%sort i
%name i T
%sort o
%name o A
%term and {_ o} {_ o} o
%prec %right 11 and
%term imp {_ o} {_ o} o
%prec %right 10 imp
%term or {_ o} {_ o} o
%prec %right 11 or
%term not {_ o} o
%prec %prefix 12 not
%term true o
%term false o
%term forall {_ {_ i} o} o
%term exists {_ {_ i} o} o
|}

(* CUT-ELIM int: cut-free intuitionistic sequent calculus.
   Ported from twelf/examples/cut_elim/int.elf.
   Builds on cut_elim_formulas (i, o, and, imp, or, not, true, false, forall, exists).
   Names introduced: hyp, conc and all sequent calculus constructors.
*)
let cut_elim_sources_2 =
  {|
%sort hyp {_ o}
%name hyp H
%sort conc {_ o}
%name conc D

%term axiom {A o} {_ hyp A} conc A
%term andr {A o} {B o} {_ conc A} {_ conc B} conc (A and B)
%term andl1 {A o} {B o} {C o} {_ {_ hyp A} conc C} {_ hyp (A and B)} conc C
%term andl2 {A o} {B o} {C o} {_ {_ hyp B} conc C} {_ hyp (A and B)} conc C
%term impr {A o} {B o} {_ {_ hyp A} conc B} conc (A imp B)
%term impl {A o} {B o} {C o} {_ conc A} {_ {_ hyp B} conc C} {_ hyp (A imp B)} conc C
%term orr1 {A o} {B o} {_ conc A} conc (A or B)
%term orr2 {A o} {B o} {_ conc B} conc (A or B)
%term orl {A o} {B o} {C o} {_ {_ hyp A} conc C} {_ {_ hyp B} conc C} {_ hyp (A or B)} conc C
%term notr {A o} {_ {p o} {_ hyp A} conc p} conc (not A)
%term notl {A o} {C o} {_ conc A} {_ hyp (not A)} conc C
%term truer conc true
%term falsel {C o} {_ hyp false} conc C
%term forallr {A {_ i} o} {_ {a i} conc (A a)} conc (forall A)
%term foralll {A {_ i} o} {C o} {T i} {_ {_ hyp (A T)} conc C} {_ hyp (forall A)} conc C
%term existsr {A {_ i} o} {T i} {_ conc (A T)} conc (exists A)
%term existsl {A {_ i} o} {C o} {_ {a i} {_ hyp (A a)} conc C} {_ hyp (exists A)} conc C
|}
