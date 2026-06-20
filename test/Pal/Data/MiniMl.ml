(* Mini-ML expression language
   Ported from twelf/examples/mini-ml/mini-ml.elf
*)
let mini_ml_exp =
  {|
%sort exp
%name exp E
%term z exp
%term s {_ exp} exp
%term case {_ exp} {_ exp} {_ {_ exp} exp} exp
%term pair {_ exp} {_ exp} exp
%term fst {_ exp} exp
%term snd {_ exp} exp
%term lam {_ {_ exp} exp} exp
%term app {_ exp} {_ exp} exp
%term letv {_ exp} {_ {_ exp} exp} exp
%term letn {_ exp} {_ {_ exp} exp} exp
%term fix {_ {_ exp} exp} exp
|}

(* Mini-ML values
   Ported from twelf/examples/mini-ml/value.elf
*)
let mini_ml_value =
  {|
%sort value {_ exp}
%term val-z value z
%term val-lam {{E}} value (lam E)
%term val-s {{V}} %if (value (s V)) %<- (value V)
%term val-pair {{V1 V2}} %if (value (pair V1 V2)) %<- (value V1) %<- (value V2)
%mode value %in
%worlds () (value _)
|}

(* Mini-ML types
   Ported from twelf/examples/mini-ml/tp.elf
*)
let mini_ml_tp =
  {|
%sort tp
%term nat tp
%term cross {_ tp} {_ tp} tp
%term arrow {_ tp} {_ tp} tp
|}

(* MINI-ML eval: natural semantics for Mini-ML.
   Ported from twelf/examples/mini_ml/eval.elf.
   Builds on mini_ml_exp (exp, z, s, case, pair, fst, snd, lam, app, letv, letn, fix).
   mini_ml_value (value/val-z/val-lam/val-s/val-pair) is also in scope.
   Names introduced: eval and ev_* constructors.
   Omitted: %terminates (eval is not total due to fix).
*)
let mini_ml_sources_eval =
  {|
%sort eval {_ exp} {_ exp}
%name eval D
%mode eval %in %out

%term ev_z eval z z
%term ev_s {{E V}} {_ eval E V} eval (s E) (s V)
%term ev_case_z {{E1 E2 E3 V}} {_ eval E1 z} {_ eval E2 V} eval (case E1 E2 E3) V
%term ev_case_s {{E1 E2 E3 V V1'}} {_ eval E1 (s V1')} {_ eval (E3 V1') V} eval (case E1 E2 E3) V
%term ev_pair {{E1 E2 V1 V2}} {_ eval E1 V1} {_ eval E2 V2} eval (pair E1 E2) (pair V1 V2)
%term ev_fst {{E V1 V2}} {_ eval E (pair V1 V2)} eval (fst E) V1
%term ev_snd {{E V1 V2}} {_ eval E (pair V1 V2)} eval (snd E) V2
%term ev_lam {{E}} eval (lam E) (lam E)
%term ev_app {{E1 E2 V V2 E1'}} {_ eval E1 (lam E1')} {_ eval E2 V2} {_ eval (E1' V2) V} eval (app E1 E2) V
%term ev_letv {{E1 E2 V V1}} {_ eval E1 V1} {_ eval (E2 V1) V} eval (letv E1 E2) V
%term ev_letn {{E1 E2 V}} {_ eval (E2 E1) V} eval (letn E1 E2) V
%term ev_fix {{E V}} {_ eval (E (fix E)) V} eval (fix E) V

%worlds () (eval _ _)
%covers eval %in %out
|}

(* MINI-ML tpinf: type inference for Mini-ML.
   Ported from twelf/examples/mini_ml/tpinf.elf.
   Builds on mini_ml_exp + mini_ml_tp (tp, nat, cross, arrow).
   Names introduced: of and tp_* constructors.
   %block l : some {T:tp} block {x:exp} {d:of x T} -> %block l [T tp] {x exp} {d of x T}
*)
let mini_ml_sources_tpinf =
  {|
%sort of {_ exp} {_ tp}
%name of P
%mode of %in %star

%term tp_z of z nat
%term tp_s {{E}} {_ of E nat} of (s E) nat
%term tp_case {{E1 E2 E3 T}} {_ of E1 nat} {_ of E2 T} {_ {x exp} {_ of x nat} of (E3 x) T} of (case E1 E2 E3) T
%term tp_pair {{E1 E2 T1 T2}} {_ of E1 T1} {_ of E2 T2} of (pair E1 E2) (cross T1 T2)
%term tp_fst {{E T1 T2}} {_ of E (cross T1 T2)} of (fst E) T1
%term tp_snd {{E T1 T2}} {_ of E (cross T1 T2)} of (snd E) T2
%term tp_lam {{E T1 T2}} {_ {x exp} {_ of x T1} of (E x) T2} of (lam E) (arrow T1 T2)
%term tp_app {{E1 E2 T1 T2}} {_ of E1 (arrow T2 T1)} {_ of E2 T2} of (app E1 E2) T1
%term tp_letv {{E1 E2 T1 T2}} {_ of E1 T1} {_ {x exp} {_ of x T1} of (E2 x) T2} of (letv E1 E2) T2
%term tp_letn {{E1 E2 T1 T2}} {_ of E1 T1} {_ of (E2 E1) T2} of (letn E1 E2) T2
%term tp_fix {{E T}} {_ {x exp} {_ of x T} of (E x) T} of (fix E) T

%block l [T tp] {x exp} {d of x T}
%worlds (l) (of _ _)
|}
