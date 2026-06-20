let fol1 =
  {|
%. First-Order Logic
Fragment with implication, negation, universal quantification.

Author: Frank Pfenning

This code is from the article

  Logical Frameworks
  Handbook of Automated Reasoning
  Alan Robinson and Andrei Voronkov, editors
  Chapter 16
  Elsevier Science and MIT Press
  In preparation

%sort i
%sort o

Formulas

%term imp {_ o} {_ o} o
%prec %right 10 imp
%term not {_ o} o
%prec %prefix 12 not
%term forall %pi (%pi i %-> o) %-> o %.

Natural deductions

%sort nd {_ o}

%term impi {{A B}} {_ {_ nd A} nd B} nd (A imp B)
%term impe {{A B}} {_ nd (A imp B)} {_ nd A} nd B

%term noti {{A}} {_ {p o} {_ nd A} nd p} nd (not A)
%term note {{A}} {_ nd (not A)} {C o} {_ nd A} nd C

%term foralli {{A}} {_ {a i} nd (A a)} nd (forall A)
%term foralle {{A}} {_ nd (forall A)} {T i} nd (A T)

%block lnd [A o] {u nd A}
%block lo {_ o}
%block li {_ i}

%worlds (lnd lo li) (nd A)
|}

let fol2 =
  {|

%. Example


%. Hilbert deductions

%sort hil {_ o}

%term k {{A B}} hil (A imp (B imp A))
%term s {{A B C}} hil ((A imp (B imp C)) imp ((A imp B) imp (A imp C)))

%term n1 {{A B}} hil ((A imp (not B)) imp ((A imp B) imp (not A)))
%term n2 {{A B}} hil ((not A) imp (A imp B))

%term f1 {T i} hil ((forall [x i] A x) imp (A T))
%term f2 {{A B}} hil ((forall [x i] (B imp A x)) imp (B imp forall [x i] A x))

%term mp {{A B}} {_ hil (A imp B)} {_ hil A} hil B
%term ug {{A}} {_ {a i} hil (A a)} hil (forall [x i] A x)

%worlds (li) (hil A)

|}

let fol3_1 =
  {|

%. Local reductions

%sort ==>R {_ nd _A} {_ nd _A}
%prec %none 14 ==>R

|}

let fol3_2_1 =
  {|
%term redl_imp {{A D E}} (impe (impi [u nd A] D u) E) ==>R (D E)

|}

let fol3_2_2 =
  {|
%term redl_not {{A C D E}} (note (noti [p o] [u nd A] D p u) C E) ==>R (D C E)

|}

let fol3_2_3 =
  {|
%term redl_forall {{D T}} (foralle (foralli [a i] D a) T) ==>R (D T)

|}

let fol3_2 = fol3_2_1 ^ fol3_2_2 ^ fol3_2_3

let fol3_3 =
  {|

%. Local expansions

%sort ==>E {_ nd A} {_ nd A}
%prec %none 14 ==>E
|}

let fol3_4 =
  {|

%term expl_imp {{A B}} {D nd (A imp B)} D ==>E (impi [u nd A] impe D u)
%term expl_not {{A}} {D nd (not A)} D ==>E (noti [p] [u nd A] note D p u)
%term expl_forall {{A}} {D nd (forall A)} D ==>E (foralli [a] foralle D a)

|}

let fol3 = fol3_1 ^ fol3_2 ^ fol3_3 ^ fol3_4

let fol4_1 =
  {|
%. Sequent calculus search result

%def dn (nd (A imp not not A)) (impi [u nd A] noti [p] [w] note w p u)

%. Translating Hilbert derivations to natural deductions

%sort hilnd {_ hil A} {_ nd A}

%term hnd_k {{A B}} hilnd k (impi [u nd A] impi [v nd B] u)
%term hnd_s {{A B C}} hilnd s (impi [u nd (A imp B imp C)] impi [v] impi [w nd A] impe (impe u w) (impe v w))

%term hnd_n1 hilnd n1 (impi [u] impi [v] noti [p] [w] note (impe u w) p (impe v w))

%term hnd_n2 {{A B}} hilnd n2 (impi [u] impi [v] note u B v)
%term hnd_f1 {{A T}} hilnd (f1 T) (impi [u nd (forall [x i] A x)] foralle u T)

%term hnd_f2 {{A B}} hilnd f2 (impi [u] impi [v] foralli [a] impe (foralle u a) v)

%term hnd_mp {{A B}} {H1 hil (A imp B)} {H2 hil A} {D1 nd (A imp B)} {D2 nd A} {_ hilnd H1 D1} {_ hilnd H2 D2} hilnd (mp H1 H2) (impe D1 D2)

%term hnd_ug {{A}} {H1 {a i} hil (A a)} {D1 {a i} nd (A a)} {_ {a i} hilnd (H1 a) (D1 a)} hilnd (ug H1) (foralli D1)
|}

(* %mode {%in x hil _A} {%out y nd _A} hilnd x y *)
let fol4_2 =
  {|
%mode {%in X _} {%out Y _} hilnd X Y
%worlds (li) (hilnd H D)
%terminates H (hilnd H _)
%covers hilnd %in %out
%total H (hilnd H _)

%? hilnd (mp (mp s k) k) D

%def _ (nd (A imp A))
    (impe
      (impe
        (impi [u]
          impi [v]
          impi [w] impe (impe u w) (impe v w))
        (impi [u] impi [v] u))
      (impi [u] impi [v] u))

      |}

let fol4 = fol4_1 ^ fol4_2

let fol5_1 =
  {|

The deduction theorem for Hilbert derivations

%sort ded {_ {_ hil A} hil B} {_ hil (A imp B)}

%term ded_id {{A}} ded ([u hil A] u) (mp (mp s k) (%the (hil (A imp (A imp A))) k))

%term ded_k {{A B}} ded ([u] k) (mp k k)
%term ded_s {{A B C}} ded ([u] s) (mp k s)

%term ded_n1 {{A B}} ded ([u] n1) (mp k n1)
%term ded_n2 {{A B}} ded ([u] n2) (mp k n2)

%term ded_f1 {{A B T}} ded ([u] f1 T) (mp k (f1 T))
%term ded_f2 {{A B}} ded ([u] f2) (mp k f2)

%term ded_mp {{A B C}} {H1 {_ hil A} hil (B imp C)} {H2 {_ hil A} hil B} {H1' hil (A imp (B imp C))} {H2' hil (A imp B)} {_ ded H1 H1'} {_ ded H2 H2'} ded ([u] mp (H1 u) (H2 u)) (mp (mp s H1') H2')

%term ded_ug {{A B H1 H1'}} {_ {a i} ded ([u] H1 u a) (H1' a)} ded ([u] ug (H1 u)) (mp f2 (ug H1'))
|}

let fol5_2 =
  {|
%block lded [A o] {u nd A} {v hil A} {h {C o} ded ([w hil C] v) (mp k v)}

%mode ded %in %out
%worlds (li lo lded) (ded H H')
%terminates H (ded H _)
%covers ded %in %out
%total H (ded H _)

|}

let fol5 = fol5_1 ^ fol5_2

let fol6_1 =
  {|

Mapping natural deductions to Hilbert derivations.

%sort ndhil {_ nd A} {_ hil A}

%term ndh_impi {{A1 B C D1 H1 H1' H1''}} {_ ded H1 H1'} {_ {u nd A1} {v hil A1} {_ {C o} ded ([w hil C] v) (mp k v)} {_ ndhil u v} ndhil (D1 u) (H1 v)} ndhil (impi D1) H1'

%term ndh_impe {{A B D1 D2 H1 H2}} {_ ndhil D1 H1} {_ ndhil D2 H2} ndhil (impe D1 D2) (mp H1 H2)

%term ndh_noti {{A1 H1 H1' H1'' D1}} {_ ded (H1 (not A1)) H1'} {_ ded (H1 A1) H1''} {_ {p o} {u nd A1} {v hil A1} {_ {C o} ded ([w hil C] v) (mp k v)} {_ ndhil u v} ndhil (D1 p u) (H1 p v)} ndhil (noti D1) (mp (mp n1 H1') H1'')

%term ndh_note {{A C D1 D2 H1 H2}} {_ ndhil D1 H1} {_ ndhil D2 H2} ndhil (note D1 C D2) (mp (mp n2 H1) H2)

%term ndh_foralli {{A D1 H1}} {_ {a i} ndhil (D1 a) (H1 a)} ndhil (foralli D1) (ug H1)

%term ndh_foralle {{A T D1 H1}} {_ ndhil D1 H1} ndhil (foralle D1 T) (mp (f1 T) H1)
|}

let fol6_2 =
  {|
%mode {%in X _} {%out Y _} ndhil X Y
%block lndhil [A o] {u nd A} {v hil A} {h {C o} ded ([w hil C] v) (mp k v)} {nh ndhil u v}
%worlds (li lo lndhil) (ndhil D H)
%terminates D (ndhil D _)
%covers ndhil %in %out
%total D (ndhil D _)


|}

let fol6 = fol6_1 ^ fol6_2
