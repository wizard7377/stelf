(* POPLMARK-1A: F-sub subtyping syntax-only chunk.
   Ported from twelf/examples/poplmark/1a.elf (syntax declarations only).
   Dropped: all proof families (trans*, narrow*, reflx, soundness, completeness)
   because they use %block some {...} block {...} which is not supported.
   Nat is needed for the mutual induction measure.
*)
let poplmark_1a_syntax =
  {|
%sort tp
%name tp T
%term top tp
%term arrow {_ tp} {_ tp} tp
%term forall {_ tp} {_ {_ tp} tp} tp

%sort assm {_ tp} {_ tp}
%sort sub {_ tp} {_ tp}

%term sub_top {{T}} sub T top
%term sub_refl {{X}} %if (sub X X) %<- (assm X _)
%term sub_trans {{X U T}} %if (sub X T) %<- (assm X U) %<- (sub U T)
%term sub_arrow {{S1 S2 T1 T2}} %if (sub (arrow S1 S2) (arrow T1 T2)) %<- (sub T1 S1) %<- (sub S2 T2)
%term sub_forall {{S1 S2 T1 T2}} %if (sub (forall S1 S2) (forall T1 T2)) %<- (sub T1 S1) %<- ({x tp} {_ assm x T1} sub (S2 x) (T2 x))

%sort var {_ tp}
%sort false

%sort nat
%name nat N
%term z nat
%term s {_ nat} nat

%sort nat_eq {_ nat} {_ nat}
%term nat_eq_ {{N}} nat_eq N N
|}

(* POPLMARK-2A: System Fw subtyping syntax-only chunk.
   Ported from twelf/examples/poplmark/2a.elf (syntax + typing declarations only).
   Relies on POPLMARK-1A's tp/top/arrow/forall being in global scope from the prior test.
   Adds: sub_tp declarative subtyping, term/value/of typing for System Fw terms.
   Dropped: sub_tp_forall (higher-order premise causes reconstruction failure),
   of_tabs, of_tapp (involve forall which needs higher-order sub_tp_forall).
*)
let poplmark_2a_syntax =
  {|
%sort sub_tp {_ tp} {_ tp}
%name sub_tp T
%term sub_tp_top {{T}} sub_tp T top
%term sub_tp_refl {{T}} sub_tp T T
%term sub_tp_trans {{T1 T2 T3}} %if (sub_tp T1 T3) %<- (sub_tp T1 T2) %<- (sub_tp T2 T3)
%term sub_tp_arrow {{S1 S2 T1 T2}} %if (sub_tp (arrow S1 S2) (arrow T1 T2)) %<- (sub_tp T1 S1) %<- (sub_tp S2 T2)

%sort term
%name term E
%term abs {_ tp} {_ {_ term} term} term
%term app {_ term} {_ term} term
%term tabs {_ tp} {_ {_ tp} term} term
%term tapp {_ term} {_ tp} term

%sort value {_ term}
%term value_abs {{T E}} value (abs T E)
%term value_tabs {{T E}} value (tabs T E)

%sort of {_ term} {_ tp}
%term of_abs {{T1 T2 E}} {_ {x term} {_ of x T1} of (E x) T2} of (abs T1 E) (arrow T1 T2)
%term of_app {{E1 E2 T11 T12}} {_ of E1 (arrow T11 T12)} {_ of E2 T11} of (app E1 E2) T12
%term of_sub {{E S T}} {_ of E S} {_ sub_tp S T} of E T
|}

(* POPLMARK-1B: Record row sorts and extended subtyping.
   Ported from twelf/examples/poplmark/1b.elf (syntax block only).
   Depends on POPLMARK-1A's tp/top/arrow/forall/assm/sub/var/false/nat/z/s/nat_eq
   being in global scope (from 1a running first in the suite).
   Adds: nat_neq/less/more, plus, label, trow (row sort + constructors),
   record tp constructor, sub_trow, sub_tp, sub_tp_trow.
   Dropped: all proof families (sum_inc, commute', assoc, assoc', add, etc.)
   and %block/%reduces declarations.
*)
let poplmark_1b_syntax =
  {|
%sort nat_neq {_ nat} {_ nat}
%term nat_neq_zs {{N}} nat_neq z (s N)
%term nat_neq_sz {{N}} nat_neq (s N) z
%term nat_neq_ss {{N M}} %if (nat_neq (s N) (s M)) %<- (nat_neq N M)

%sort nat_less {_ nat} {_ nat}
%term nat_less_z {{N}} nat_less z (s N)
%term nat_less_s {{N M}} %if (nat_less (s N) (s M)) %<- (nat_less N M)

%sort nat_more {_ nat} {_ nat}
%term nat_more_z {{N}} nat_more (s N) z
%term nat_more_s {{N M}} %if (nat_more (s N) (s M)) %<- (nat_more N M)

%sort plus {_ nat} {_ nat} {_ nat}
%term plus_z {{N}} plus z N N
%term plus_s {{M N N'}} %if (plus (s M) N (s N')) %<- (plus M N N')

%sort label
%term label_nat {_ nat} label

%sort label_eq {_ label} {_ label}
%term label_eq_ {{L}} label_eq L L

%sort label_neq {_ label} {_ label}
%term label_neq_ {{N M}} %if (label_neq (label_nat N) (label_nat M)) %<- (nat_neq N M)

%sort label_less {_ label} {_ label}
%term label_less_ {{N M}} %if (label_less (label_nat N) (label_nat M)) %<- (nat_less N M)

%sort label_more {_ label} {_ label}
%term label_more_ {{N M}} %if (label_more (label_nat N) (label_nat M)) %<- (nat_more N M)

%sort trow
%term trow_nil trow
%term trow_cons {_ label} {_ tp} {_ trow} trow

%sort trow_lookup {_ label} {_ trow} {_ tp}
%term trow_lookup_yes {L label} {T tp} {TR trow} trow_lookup L (trow_cons L T TR) T
%term trow_lookup_no {L label} {L' label} {T tp} {T' tp} {TR trow} %if (trow_lookup L (trow_cons L' T' TR) T) %<- (trow_lookup L TR T)

%sort trow_labelfree {_ trow} {_ label}
%term trow_labelfree_nil {L label} trow_labelfree trow_nil L
%term trow_labelfree_cons {L label} {L' label} {TR trow} {T tp} %if (trow_labelfree (trow_cons L' T TR) L) %<- (label_neq L L') %<- (trow_labelfree TR L)

%sort trow_eq {_ trow} {_ trow}
%term trow_eq_ {{TR}} trow_eq TR TR

%sort trow_order {_ trow} {_ trow}
%sort trow_insert {_ label} {_ tp} {_ trow} {_ trow}

%term trow_order_nil trow_order trow_nil trow_nil
%term trow_order_cons {L label} {S tp} {SR trow} {TR trow} {TR' trow} %if (trow_order (trow_cons L S SR) TR') %<- (trow_order SR TR) %<- (trow_insert L S TR TR')

%term trow_insert_nil {L label} {S tp} trow_insert L S trow_nil (trow_cons L S trow_nil)
%term trow_insert_less {L label} {L' label} {S tp} {T tp} {TR trow} %if (trow_insert L S (trow_cons L' T TR) (trow_cons L S (trow_cons L' T TR))) %<- (label_less L L')
%term trow_insert_more {L label} {L' label} {S tp} {T tp} {TR trow} {TR' trow} %if (trow_insert L S (trow_cons L' T TR) (trow_cons L' T TR')) %<- (label_more L L') %<- (trow_insert L S TR TR')

%sort trow_uniqueness {_ trow}
%term trow_uniqueness_nil trow_uniqueness trow_nil
%term trow_uniqueness_cons {L label} {TR trow} {T tp} %if (trow_uniqueness (trow_cons L T TR)) %<- (trow_labelfree TR L) %<- (trow_uniqueness TR)

%term record {_ trow} {_ trow_uniqueness _} tp

%sort sub_trow {_ trow} {_ trow}
%term sub_trow_nil sub_trow trow_nil trow_nil
%term sub_trow_cons {L label} {S tp} {T tp} {SR trow} {TR trow} %if (sub_trow (trow_cons L S SR) (trow_cons L T TR)) %<- (sub_trow SR TR) %<- (sub S T)
%term sub_trow_cons' {L label} {S tp} {SR trow} {TR trow} %if (sub_trow (trow_cons L S SR) TR) %<- (sub_trow SR TR)

%sort sub_tp {_ tp} {_ tp}
%sort sub_tp_trow {_ trow} {_ trow}

%term sub_tp_top {{T}} sub_tp T top
%term sub_tp_refl {{T}} sub_tp T T
%term sub_tp_trans {{T1 T2 T3}} %if (sub_tp T1 T3) %<- (sub_tp T1 T2) %<- (sub_tp T2 T3)
%term sub_tp_arrow {{S1 S2 T1 T2}} %if (sub_tp (arrow S1 S2) (arrow T1 T2)) %<- (sub_tp T1 S1) %<- (sub_tp S2 T2)
%term sub_tp_forall {{S1 S2 T1 T2}} %if (sub_tp (forall S1 S2) (forall T1 T2)) %<- (sub_tp T1 S1) %<- ({x tp} {_ sub_tp x T1} sub_tp (S2 x) (T2 x))
%term sub_tp_record {SR trow} {TR trow} {SR' trow} {TR' trow} {SRuniq trow_uniqueness SR} {TRuniq trow_uniqueness TR} %if (sub_tp (record SR SRuniq) (record TR TRuniq)) %<- (trow_order SR SR') %<- (trow_order TR TR') %<- (sub_tp_trow SR' TR')

%term sub_tp_trow_nil sub_tp_trow trow_nil trow_nil
%term sub_tp_trow_cons {L label} {S tp} {T tp} {SR trow} {TR trow} %if (sub_tp_trow (trow_cons L S SR) (trow_cons L T TR)) %<- (sub_tp_trow SR TR) %<- (sub_tp S T)
%term sub_tp_trow_cons' {L label} {S tp} {SR trow} {TR trow} %if (sub_tp_trow (trow_cons L S SR) TR) %<- (sub_tp_trow SR TR)
|}

(* POPLMARK-2B: System Fw with records — syntax-only extension of 1b.
   Ported from twelf/examples/poplmark/2b.elf (syntax block only).
   Depends on POPLMARK-1B's nat/label/trow/sub_tp/sub_tp_trow in global scope.
   Adds: term sorts (term/bterm/erow/pattern/prow), basic constructors.
   Dropped: all proof families (typing, step, progress, preservation).
*)
let poplmark_2b_syntax =
  {|
%sort term
%sort bterm
%sort erow
%sort pattern
%sort prow

%term base {_ term} bterm
%term bnd {_ tp} {_ {_ term} bterm} bterm

%term abs {_ tp} {_ {_ term} term} term
%term app {_ term} {_ term} term
%term tabs {_ tp} {_ {_ tp} term} term
%term tapp {_ term} {_ tp} term

%term rec {_ erow} term
%term proj {_ term} {_ label} term
%term plet {_ pattern} {_ term} {_ bterm} term

%term erow_nil erow
%term erow_cons {_ label} {_ term} {_ erow} erow

%sort erow_lookup {_ label} {_ erow} {_ term}
%term erow_lookup_yes {L label} {E term} {ER erow} erow_lookup L (erow_cons L E ER) E
%term erow_lookup_no {L label} {L' label} {E term} {E' term} {ER erow} %if (erow_lookup L (erow_cons L' E' ER) E) %<- (erow_lookup L ER E)

%sort erow_order {_ erow} {_ erow}
%sort erow_insert {_ label} {_ term} {_ erow} {_ erow}

%term erow_order_nil erow_order erow_nil erow_nil
%term erow_order_cons {L label} {E term} {ER erow} {ER' erow} {ER'' erow} %if (erow_order (erow_cons L E ER) ER') %<- (erow_order ER ER'') %<- (erow_insert L E ER'' ER')

%term erow_insert_nil {L label} {E term} erow_insert L E erow_nil (erow_cons L E erow_nil)
%term erow_insert_less {L label} {L' label} {E term} {E' term} {ER erow} %if (erow_insert L E (erow_cons L' E' ER) (erow_cons L E (erow_cons L' E' ER))) %<- (label_less L L')
%term erow_insert_more {L label} {L' label} {E term} {E' term} {ER erow} {ER' erow} %if (erow_insert L E (erow_cons L' E' ER) (erow_cons L' E' ER')) %<- (label_more L L') %<- (erow_insert L E ER ER')

%term pat_var {_ tp} pattern
%term pat_rec {_ prow} pattern

%term prow_nil prow
%term prow_cons {_ label} {_ pattern} {_ prow} prow
|}
