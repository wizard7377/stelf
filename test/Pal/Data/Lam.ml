let lam_1 =
  {|
Lambda-Calculus Fragment of Mini-ML.
Author: Frank Pfenning

Simple types
%sort tp

%term arrow {_ tp} {_ tp} tp

%. Expressions
%sort exp

%term lam {_ {_ exp} exp} exp
%term app {_ exp} {_ exp} exp

%. Type inference
|- E : T  (expression E has type T)

%sort of {_ exp} {_ tp}
|}

let lam_2 =
  {|
%mode of %in %star

%term tp_lam {{E T1 T2}} {_ {x exp} {_ of x T1} of (E x) T2} of (lam E) (arrow T1 T2)

%term tp_app {{E1 E2 T1 T2}} {_ of E1 (arrow T2 T1)} {_ of E2 T2} of (app E1 E2) T1

%. Evaluation (call-by-value)
E ==> V  (expression E evaluates to value V)

%sort eval {_ exp} {_ exp}
%mode eval %in %out

%term ev_lam {{E}} eval (lam E) (lam E)

%term ev_app {{E1 E2 V V2 E1'}} {_ eval E1 (lam E1')} {_ eval E2 V2} {_ eval (E1' V2) V} eval (app E1 E2) V

|}

let lam_3 =
  {|
%. Regular world for type-checking
%block tp_var [T tp] {x exp} {u of x T}
%worlds (tp_var) (of E T)

%. Type inference terminates
%terminates E (of E T)

%. There is at least one typing rule for every expression
%covers of %in %star

%. Closed worlds for evaluation
%worlds () (eval E V)

%. There is at least one evaluation rule for every closed expression
%covers eval %in %out

|}

let lam_4 =
  {|
%. Type preservation as higher-level family
%sort tps {_ eval E V} {_ of E T} {_ of V T}

%term tps_lam {E {_ exp} exp} {T1 tp} {T2 tp} {P {x exp} {_ of x T1} of (E x) T2} tps ev_lam (tp_lam P) (tp_lam P)

%term tps_app {E1 exp} {E2 exp} {V exp} {V2 exp} {E1' {_ exp} exp} {T tp} {T2 tp} {D1 eval E1 (lam E1')} {D2 eval E2 V2} {D3 eval (E1' V2) V} {P1 of E1 (arrow T2 T)} {P2 of E2 T2} {Q1' {x exp} {_ of x T2} of (E1' x) T} {Q2 of V2 T2} {Q of V T} {_ tps D1 P1 (tp_lam Q1')} {_ tps D2 P2 Q2} {_ tps D3 (Q1' V2 Q2) Q} tps (ev_app D1 D2 D3) (tp_app P1 P2) Q

%. Applying type preservation
%def e0 _ (app (lam [x] x) (lam [y] y))
%? of e0 T
%? eval e0 V
|}

let lam_5 =
  {|
%. Example of regular worlds
cp copies input to output.

%sort cp {_ exp} {_ exp}

%term cp_app {E1 exp} {E2 exp} {F1 exp} {F2 exp} {_ cp E1 F1} {_ cp E2 F2} cp (app E1 E2) (app F1 F2)

%term cp_lam {E {_ exp} exp} {F {_ exp} exp} {_ {x exp} {_ cp x x} cp (E x) (F x)} cp (lam [x] E x) (lam [x] F x)

%mode cp %in %out
%block cp_var {x exp} {u cp x x}
%worlds (cp_var) (cp E _)
%total E (cp E _)
%.
Following version cannot be checked: input coverage on parameter y is violated.
It would declare cp with a block containing {x:exp} {y:exp} {u:cp x y}, but cp_lam's
higher-order premise would allow y to differ from x, which violates input coverage.

Following version also cannot be checked: output coverage on (F y) is violated.
It would add a premise cp y y -> cp (E x) (F y), meaning F y may not be covered
for the output position.

|}

let polylam =
  {|
%sort tp
%term => {_ tp} {_ tp} tp
%prec %right 10 =>
%term all {_ {_ tp} tp} tp

%sort tm {_ tp}
%term lam {{A tp}} {{B tp}} {_ {_ tm A} tm B} tm (A => B)
%term app {{A tp}} {{B tp}} {_ tm (A => B)} {_ tm A} tm B
%term tlam {{A}} {_ {a tp} tm (A a)} tm (all A)
%term tapp {{A}} {_ tm (all A)} {B tp} tm (A B)

%def nat _ (all [a tp] a => (a => a) => a)
%def zero _ (tlam [a tp] lam [z tm a] lam [s tm (a => a)] z)
%def succ _ (lam [x tm nat] tlam [a tp] lam [z tm a] lam [s tm (a => a)] app s (app (app (tapp x a) z) s))
%def succ' (tm (nat => nat)) (lam [x tm nat] tlam [a tp] lam [z tm a] lam [s tm (a => a)] app s (app (app (tapp x a) z) s))
%def plus _ (lam [x tm nat] lam [y tm nat] app (app (tapp y nat) x) succ)
%def times _ (lam [x tm nat] lam [y tm nat] app (app (tapp y nat) zero) (app plus x))
%def exp _ (lam [x tm nat] lam [y tm nat] app (app (tapp y nat) (app succ zero)) (app times x))
|}
