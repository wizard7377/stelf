(* INCLL: INCLL sorts and terms.
   Ported from twelf/examples/incll/incll.elf.
   Dropped: Twelf abbreviation syntax (`<= = [x][y] y => x` etc.).
   Dropped: `|` infix list cons (single-char identifier, may fail — using `cons` instead).
   `^` prefix also risky — using `atm_frm` instead.
*)
let incll_syntax =
  {|
%sort sort
%term arrow {_ sort} {_ sort} sort
%term cross {_ sort} {_ sort} sort

%sort trm {_ sort}
%term app {{A B}} {_ trm (arrow A B)} {_ trm A} trm B
%term lam {{A B}} {_ {_ trm A} trm B} trm (arrow A B)
%term pair {{A B}} {_ trm A} {_ trm B} trm (cross A B)

%sort eval {_ trm _A} {_ trm _A}
%term eval_lam {{A B E}} eval (lam E) (lam E)
%term eval_app {{A B E E' V V'}} %if (eval (app (lam E) E') V) %<- (eval E' V') %<- (eval (E V') V)

%sort atm
%sort frm
%term int sort

%term 1 trm int
%term 2 trm int
%term 3 trm int
%term 4 trm int
%term 5 trm int

%sort list_sort {_ sort}
%term list_sort/nil {{A}} list_sort A
%term list_sort/cons {{A}} {_ trm A} {_ list_sort A} list_sort A

%sort frm_atm {_ atm}
%term atm_frm {_ atm} frm

%sort imp {_ frm} {_ frm}
%term imp_i {_ frm} {_ frm} frm

%term forall {A sort} {_ {_ trm A} frm} frm
%term forall2 {A1 sort} {A2 sort} {_ {_ {_ trm A1} trm A2} frm} frm
|}
