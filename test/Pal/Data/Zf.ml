let zf_1 = {|

%sort prop
%sort pf {_ prop}
%sort set
|}

let zf_2 =
  {|
%term false prop
%term imp {_ prop} {_ prop} prop
%term all {_ {_ set} prop} prop
%term eq {_ set} {_ set} prop
%term in {_ set} {_ set} prop
|}

let zf_3 =
  {|
%def not ({_ prop} prop) ([a] imp a false) %.
%def and ({_ prop} {_ prop} prop) ([a][b] not (imp a (not b))) %.
%def or ({_ prop} {_ prop} prop) ([a][b] imp (not a) b) %.
%def iff ({_ prop} {_ prop} prop) ([a][b] and (imp a b) (imp b a)) %.
%def ex ({_ {_ set} prop} prop) ([p] not(all([z]not (p z)))) %.
%def unique ({_ {_ set} prop} prop) ([p] all([z] imp (p z) (all ([z'] imp (p z') (eq z z'))))) %.
%def ex_unique ({_ {_ set} prop} prop) ([p] and (ex p) (unique p)) %.
|}

let zf_4 =
  {|

%term imp_i {_ {_ pf _A} pf _B} pf (imp _A _B) %.
%term imp_e {_ pf (imp _A _B)} {_ pf _A} pf _B %.
%term all_i {_ {z} pf (_P z)} pf (all _P) %.
%term all_e {_ pf (all _P)} {z set} pf (_P z) %.
%term classical {_ pf (not(not _A))} pf _A %.
%term eq_i pf (eq _A _A) %.
%term eq_e {_ pf (eq _A _B)} {s {_ set} prop} {_ pf (s _A)} pf (s _B) %.
%term if {_ prop} {_ set} {_ set} set
%term if_then {_ pf _P} pf (eq (if _P _X _Y) _X) %.
%term if_else {_ pf (not _P)} pf (eq (if _P _X _Y) _Y) %.
%term empty    set %.
%term double   {_ set} {_ set} set %.
%term unions   {_ set} set %.
%term powerset {_ set} set %.
%term replace  {_ set} {_ {_ set} set} set %.
%term omega    set %.
|}

let zf_5 =
  {|
%def single ({_ set} set) [x] double x x %.
%def restrict ({_ set} {_ {_ set} prop} set) [x][q] unions (replace x ([z] if (q z) (single z) empty)) %.
%def inter ({_ set} {_ set} set) [x][y] restrict x ([z] in z y) %.
%def union ({_ set} {_ set} set) [x][y] unions (double x y) %.
%def zero set empty %.
%def succ ({_ set} set) [x] union x (single x) %.
%def subset ({_ set} {_ set} prop) [x][y]all[z] imp (in z x) (in z y) %.
%def disjoint ({_ set} {_ set} prop) [x][y] eq (inter x y) empty %.
%def omega_closed ({_ set} prop) [x] and (in empty x) (all [n] imp (in n x) (in (succ n) x)) %.
|}

let zf_6 =
  {|
%term extensionality pf (iff (eq _X _Y) (all[z] iff (in z _X) (in z _Y))) %.
%term foundation     pf (ex([z] and (in z _X) (disjoint z _X))) %.
%term emtpy_ax       pf (not (in _X empty)) %.
%term double_ax      pf (iff (in _Z (double _X _Y)) (or (in _Z _X) (in _Z _Y))) %.
%term union_ax       pf (iff (in _Z (unions _X)) (ex[y] and (in _Z y) (in y _X))) %.
%term powerset_ax    pf (iff (in _Z (powerset _X)) (subset _Z _X)) %.
%term replace_ax     pf (iff (in _Z (replace _X F)) (ex[y] and (in y _X) (eq _Z (F y)))) %.
%term omega_ax       pf (and (omega_closed omega)
		          (all[o] imp (omega_closed o) (subset omega o))) %.
%term choice_ax      pf
(imp (all[y1] imp (in y1 _X)
      (all[y2] imp (in y2 _X) (disjoint y1 y2)))
   (ex [x'](all[y] imp (in y _X)
		 (ex_unique ([y'] (and (in y' x') (in y' y))))))) %.
|}
