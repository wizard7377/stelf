(* CCC: Cartesian closed category syntax.
   Ported from twelf/examples/ccc/ccc.elf.
   Renamed: `1` (terminal obj) → `unit_obj`, `*` (product) → `prod`, `@` → `comp`,
   `==` (morphism equality) → `meq`, `=>` (exponential) → `exp_obj`.
   Note: no %prec declarations — all operators used in prefix form to avoid
   "Leading infix operator" parse errors that occur when infix is mixed with prefix.
*)
let ccc_syntax =
  {|
%sort obj
%name obj _A
%sort mor {_ obj} {_ obj}
%name mor _F
%sort meq {_ mor _A _B} {_ mor _A _B}
%name meq _ME

%term id {{A}} mor A A
%term comp {{A B C}} {_ mor B C} {_ mor A B} mor A C

%term meq_refl {{A B F}} meq F F
%term meq_then {{A B F F' F''}} {_ meq F F'} {_ meq F' F''} meq F F''
%term meq_sym {{A B F F'}} {_ meq F F'} meq F' F

%term eq_comp {{A B C F F' G G'}} {_ meq F F'} {_ meq G G'} meq (comp F G) (comp F' G')

%term id_l {{A B F}} meq (comp id F) F
%term id_r {{A B F}} meq (comp F id) F
%term assoc {{A B C D F G H}} meq (comp H (comp G F)) (comp (comp H G) F)

%term unit_obj obj
%term prod {_ obj} {_ obj} obj

%term drop {{A}} mor A unit_obj
%term fst {{A B}} mor (prod A B) A
%term snd {{A B}} mor (prod A B) B
%term pair_mor {{A B C}} {_ mor A B} {_ mor A C} mor A (prod B C)

%term eq_pair {{A B C F F' G G'}} {_ meq F F'} {_ meq G G'} meq (pair_mor F G) (pair_mor F' G')
%term prod_l {{A B C F G}} meq (comp fst (pair_mor F G)) F
%term prod_r {{A B C F G}} meq (comp snd (pair_mor F G)) G
%term prod_u {{A B C H}} meq (pair_mor (comp fst H) (comp snd H)) H

%term exp_obj {_ obj} {_ obj} obj

%term app_mor {{B C}} mor (prod (exp_obj B C) B) C
%term cur {{A B C}} {_ mor (prod A B) C} mor A (exp_obj B C)

%term eq_cur {{A B C F F'}} {_ meq F F'} meq (cur F) (cur F')
%term exp_e {{A B C F}} meq (comp app_mor (pair_mor (comp (cur F) fst) snd)) F
%term exp_u {{A B C G}} meq (cur (comp app_mor (pair_mor (comp G fst) snd))) G
|}

(* ccc/spass.elf: CCC with categorical laws, products, exponentials, and lemmas.
   Same approach as ccc_syntax: all operators renamed to avoid infix parse errors.
   spass_meq replaces ==, spass_comp replaces @, spass_prod_obj replaces *, spass_exp_obj replaces =>.
   spass_meq uses implicit free-variable indices (same pattern as ccc_syntax meq).
   Additional lemma terms: spass_distp, spass_appl, spass_distc. *)
let ccc_spass_1 =
  {|
%sort spass_obj
%sort spass_mor {_ spass_obj} {_ spass_obj}
%sort spass_meq {_ spass_mor _SA _SB} {_ spass_mor _SA _SB}
%term spass_id {A spass_obj} spass_mor A A
%term spass_comp {{A B C}} {_ spass_mor B C} {_ spass_mor A B} spass_mor A C
%term spass_refl {{SA SB F}} spass_meq F F
%term spass_then {{SA SB F F' F''}} {_ spass_meq F F'} {_ spass_meq F' F''} spass_meq F F''
%term spass_sym {{SA SB F F'}} {_ spass_meq F F'} spass_meq F' F
%term spass_ceq {{SA SB SC F F' G G'}} {_ spass_meq F F'} {_ spass_meq G G'} spass_meq (spass_comp F G) (spass_comp F' G')
%term spass_id_l {{SA SB F}} spass_meq (spass_comp spass_id F) F
%term spass_id_r {{SA SB F}} spass_meq (spass_comp F spass_id) F
%term spass_ass {{SA SB SC SD F G H}} spass_meq (spass_comp H (spass_comp G F)) (spass_comp (spass_comp H G) F)
%term spass_unit_obj spass_obj
%term spass_prod_obj {_ spass_obj} {_ spass_obj} spass_obj
%term spass_drop {A spass_obj} spass_mor A spass_unit_obj
%term spass_fst {{A B}} spass_mor (spass_prod_obj A B) A
%term spass_snd {{A B}} spass_mor (spass_prod_obj A B) B
%term spass_pair {{A B C}} {_ spass_mor A B} {_ spass_mor A C} spass_mor A (spass_prod_obj B C)
%term spass_peq {{A B C F F' G G'}} {_ spass_meq F F'} {_ spass_meq G G'} spass_meq (spass_pair F G) (spass_pair F' G')
%term spass_term_u {{A H}} spass_meq H spass_drop
%term spass_prod_l {{A B C F G}} spass_meq (spass_comp spass_fst (spass_pair F G)) F
%term spass_prod_r {{A B C F G}} spass_meq (spass_comp spass_snd (spass_pair F G)) G
%term spass_prod_u {{A B C H}} spass_meq (spass_pair (spass_comp spass_fst H) (spass_comp spass_snd H)) H
%term spass_exp_obj {_ spass_obj} {_ spass_obj} spass_obj
%term spass_app {{B C}} spass_mor (spass_prod_obj (spass_exp_obj B C) B) C
%term spass_cur {{A B C}} {_ spass_mor (spass_prod_obj A B) C} spass_mor A (spass_exp_obj B C)
%term spass_ceq2 {{A B C F F'}} {_ spass_meq F F'} spass_meq (spass_cur F) (spass_cur F')
%term spass_exp_e {{A B C F}} spass_meq (spass_comp spass_app (spass_pair (spass_comp (spass_cur F) spass_fst) spass_snd)) F
%term spass_exp_u {{A B C G}} spass_meq (spass_cur (spass_comp spass_app (spass_pair (spass_comp G spass_fst) spass_snd))) G
%term spass_distp {{A B C D F G H}} spass_meq (spass_comp (spass_pair F G) H) (spass_pair (spass_comp F H) (spass_comp G H))
%term spass_appl {{A B C D F G H}} spass_meq (spass_comp spass_app (spass_pair (spass_comp (spass_cur F) G) H)) (spass_comp F (spass_pair G H))
%term spass_distc {{A B C D F G}} spass_meq (spass_comp (spass_cur F) G) (spass_cur (spass_comp F (spass_pair (spass_comp G spass_fst) spass_snd)))
|}
