let jsf_1 =
  {|
Judgmental S4
[A judgmental reconstruction of modal logic, F.Pfenning and R.Davies,
 MSCS 11:511-540, 2001]

Representation with intrinsic types, worlds,
but not a Kripke semantics

Idea: Translate the judgment
  u1::B1,...,un::Bn ; x1:A1,...,xm:Am |- J
as
  u1:{W'}tm B1 W',...,un:{W'}tm Bn W', ---,
  x1:tm A1 W,...,xm:tm Am W |- J*

where "---" are assumptions y:tm B W' for W' <> W
and if J = (M : A) then J* = M* : tm A W
    if J = (E - A) then J* = E* : exp A W

%sort tp
%term => {_ tp} {_ tp} tp
%term box {_ tp} tp
%term dia {_ tp} tp
%prec %right 10 =>

%sort world

%sort tm {_ tp} {_ world}
%sort exp {_ tp} {_ world}

%term lam {{A B W}} {_ {_ tm A W} tm B W} tm (A => B) W
%term app {{A B W}} {_ tm (A => B) W} {_ tm A W} tm B W
%term boxi {{A W}} {_ {w world} tm A w} tm (box A) W
%term boxe {{A C W}} {_ tm (box A) W} {_ {_ {W' world} tm A W'} tm C W} tm C W
%term t2e {{A W}} {_ tm A W} exp A W
%term diai {{A W}} {_ exp A W} tm (dia A) W
%term diae {{A C W}} {_ tm (dia A) W} {_ {w world} {_ tm A w} exp C w} exp C W
%term boxep {{A C W}} {_ tm (box A) W} {_ {_ {W' world} tm A W'} exp C W} exp C W
%sort subdia {_ exp A W} {_ {w world} {_ tm A w} exp C w} {_ exp C W}
|}

let jsf_2_1 = {|
%mode {%in X _} {%in Y _} {%out Z _} subdia X Y Z
|}

let jsf_2_2 =
  {|
%term sdt2e {A tp} {C tp} {W world} {M tm A W} {F {w world} {_ tm A w} exp C w} subdia (t2e M) ([w] [x] F w x) (F W M)

%term sddiae {A tp} {B tp} {C tp} {W world} {M tm (dia A) W} {E {v world} {_ tm A v} exp B v} {F {w world} {_ tm B w} exp C w} {F' {v world} {_ tm A v} exp C v} {_ {v world} {y tm A v} subdia (E v y) ([w] [x] F w x) (F' v y)} subdia (diae M [v] [y] E v y) ([w] [x] F w x) (diae M [v] [y] F' v y)

%term sdboxep {A tp} {C tp} {D tp} {W world} {M tm (box A) W} {E {u {V world} tm A V} exp C W} {F {w world} {_ tm C w} exp D w} {F' {u {V world} tm A V} exp D W} {_ {u {V world} tm A V} subdia (E u) ([w] [x] F w x) (F' u)} subdia (boxep M [u] E u) ([w] [x] F w x) (boxep M [u] F' u)
|}

let jsf_3 =
  {|
%block by [B tp] {v world} {y tm B v}
%block bu [B tp] {u {V world} tm B V}
%worlds (by bu) (subdia E F F')
%total E (subdia E F _) %.

This does not work, unfortunately:
The "str" strengthening lemma would require handling cases like strlam where a bound
variable y2 of type tm C2 w appears free in the conclusion, but w is also quantified
by the str family. The main issue is that the case for str ([x][w] y2) ([w] y2) cannot
be typed because y2 has type tm C2 w but w is the variable we are quantifying over.
|}

let jsf_4 =
  {|
Examples

%def _ (tm (box A => A) W) (lam [x] boxe x [u] u W)
%def _ (tm (box A => box (box A)) W) (lam [x] boxe x [u] boxi [w] boxi [w'] u w')
%def _ (tm (box (A => B) => box A => box B) W) (lam [x] lam [y] boxe x [u] boxe y [v] boxi [w] app (u w) (v w))
%def _ (tm (A => dia A) W) (lam [x] diai (t2e x))
%def _ (tm (dia (dia A) => dia A) W) (lam [x] diai (diae x [w] [y] diae y [v] [z] t2e z))
%def _ (tm (box (A => B) => dia A => dia B) W) (lam [x] lam [y] diai (boxep x [u] diae y [w] [z] t2e (app (u w) z)))
%.
Counterexamples, all must fail:
The following would require box to be a comonad (A => box A), but this is not valid in S4.
The term (lam [x] boxi [w] x) fails because x has type tm A W but we need tm A w for
arbitrary w, which would require the structural rule for modal contexts.
Similarly (lam [x] diae x [w][y] t2e y) fails because y has type tm A w but we need
tm A W for the current world W.
The term for (dia (A => B) => dia A => dia B) fails because dia is not "normal" in S4.
The term (dia A => box B) => box (A => B) is true in Kripke semantics a la Simpson but
not in the judgmental formulation.
The two S5 theorems (dia A => box (dia A)) and (dia (box A) => box A) both fail because
S4 does not have the symmetry or Euclidean properties needed for S5.
|}
