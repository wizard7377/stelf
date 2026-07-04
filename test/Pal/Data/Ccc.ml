(* CCC: Cartesian closed category syntax.
   Ported from twelf/examples/ccc/ccc.elf.
   Renamed: `1` (terminal obj) → `unit-obj`, `*` (product) → `prod`, `@` → `comp`,
   `==` (morphism equality) → `meq`, `=>` (exponential) → `exp-obj`.
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

%term unit-obj obj
%term prod {_ obj} {_ obj} obj

%term drop {{A}} mor A unit-obj
%term fst {{A B}} mor (prod A B) A
%term snd {{A B}} mor (prod A B) B
%term pair_mor {{A B C}} {_ mor A B} {_ mor A C} mor A (prod B C)

%term eq_pair {{A B C F F' G G'}} {_ meq F F'} {_ meq G G'} meq (pair_mor F G) (pair_mor F' G')
%term prod_l {{A B C F G}} meq (comp fst (pair_mor F G)) F
%term prod_r {{A B C F G}} meq (comp snd (pair_mor F G)) G
%term prod_u {{A B C H}} meq (pair_mor (comp fst H) (comp snd H)) H

%term exp-obj {_ obj} {_ obj} obj

%term app_mor {{B C}} mor (prod (exp-obj B C) B) C
%term cur {{A B C}} {_ mor (prod A B) C} mor A (exp-obj B C)

%term eq_cur {{A B C F F'}} {_ meq F F'} meq (cur F) (cur F')
%term exp_e {{A B C F}} meq (comp app_mor (pair_mor (comp (cur F) fst) snd)) F
%term exp_u {{A B C G}} meq (cur (comp app_mor (pair_mor (comp G fst) snd))) G
|}

(* ccc/spass.elf: CCC with categorical laws, products, exponentials, and lemmas.
   Same approach as ccc_syntax: all operators renamed to avoid infix parse errors.
   spass-meq replaces ==, spass-comp replaces @, spass-prod-obj replaces *, spass-exp-obj replaces =>.
   spass-meq uses implicit free-variable indices (same pattern as ccc_syntax meq).
   Additional lemma terms: spass-distp, spass-appl, spass-distc. *)
let ccc_spass_1 =
  {|
%sort spass-obj
%sort spass-mor {_ spass-obj} {_ spass-obj}
%sort spass-meq {_ spass-mor _SA _SB} {_ spass-mor _SA _SB}
%term spass-id {{A}} spass-mor A A
%term spass-comp {{A B C}} {_ spass-mor B C} {_ spass-mor A B} spass-mor A C
%term spass-refl {{SA SB F}} spass-meq F F
%term spass-then {{SA SB F F' F''}} {_ spass-meq F F'} {_ spass-meq F' F''} spass-meq F F''
%term spass-sym {{SA SB F F'}} {_ spass-meq F F'} spass-meq F' F
%term spass-ceq {{SA SB SC F F' G G'}} {_ spass-meq F F'} {_ spass-meq G G'} spass-meq (spass-comp F G) (spass-comp F' G')
%term spass-id_l {{SA SB F}} spass-meq (spass-comp spass-id F) F
%term spass-id_r {{SA SB F}} spass-meq (spass-comp F spass-id) F
%term spass-ass {{SA SB SC SD F G H}} spass-meq (spass-comp H (spass-comp G F)) (spass-comp (spass-comp H G) F)
%term spass-unit-obj spass-obj
%term spass-prod-obj {_ spass-obj} {_ spass-obj} spass-obj
%term spass-drop {{A}} spass-mor A spass-unit-obj
%term spass-fst {{A B}} spass-mor (spass-prod-obj A B) A
%term spass-snd {{A B}} spass-mor (spass-prod-obj A B) B
%term spass-pair {{A B C}} {_ spass-mor A B} {_ spass-mor A C} spass-mor A (spass-prod-obj B C)
%term spass-peq {{A B C F F' G G'}} {_ spass-meq F F'} {_ spass-meq G G'} spass-meq (spass-pair F G) (spass-pair F' G')
%term spass-term_u {{A H}} spass-meq H spass-drop
%term spass-prod_l {{A B C F G}} spass-meq (spass-comp spass-fst (spass-pair F G)) F
%term spass-prod_r {{A B C F G}} spass-meq (spass-comp spass-snd (spass-pair F G)) G
%term spass-prod_u {{A B C H}} spass-meq (spass-pair (spass-comp spass-fst H) (spass-comp spass-snd H)) H
%term spass-exp-obj {_ spass-obj} {_ spass-obj} spass-obj
%term spass-app {{B C}} spass-mor (spass-prod-obj (spass-exp-obj B C) B) C
%term spass-cur {{A B C}} {_ spass-mor (spass-prod-obj A B) C} spass-mor A (spass-exp-obj B C)
%term spass-ceq2 {{A B C F F'}} {_ spass-meq F F'} spass-meq (spass-cur F) (spass-cur F')
%term spass-exp_e {{A B C F}} spass-meq (spass-comp spass-app (spass-pair (spass-comp (spass-cur F) spass-fst) spass-snd)) F
%term spass-exp_u {{A B C G}} spass-meq (spass-cur (spass-comp spass-app (spass-pair (spass-comp G spass-fst) spass-snd))) G
%term spass-distp {{A B C D F G H}} spass-meq (spass-comp (spass-pair F G) H) (spass-pair (spass-comp F H) (spass-comp G H))
%term spass-appl {{A B C D F G H}} spass-meq (spass-comp spass-app (spass-pair (spass-comp (spass-cur F) G) H)) (spass-comp F (spass-pair G H))
%term spass-distc {{A B C D F G}} spass-meq (spass-comp (spass-cur F) G) (spass-cur (spass-comp F (spass-pair (spass-comp G spass-fst) spass-snd)))
|}
