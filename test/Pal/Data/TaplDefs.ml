(* TAPL-DEFS: tapl_ch13/defs.elf (STLC with references — syntax-only chunk)
   Ported from twelf/examples/tapl_ch13/defs.elf.
   Note: Uses unique prefixes to avoid conflicts with earlier suite declarations.
   `tp` → `ref_tp`, `exp` → `ref_exp` to avoid clashes with SMALL-STEP-LAM/CRARY-EXCON.
   `nat`, `z`, `s` re-used from earlier suites (already in scope).
   `=>` already infix-left 5 from SMALL-STEP-LAM; used that way here.
   Dropped: %freeze (var sort not included), %terminates {}, %unique, step/typing rules.
*)
let tapl_defs_types =
  {|
%sort ref_tp
%name ref_tp T
%term ref_arrow {_ ref_tp} {_ ref_tp} ref_tp
%term unit_tp ref_tp
%term ref {_ ref_tp} ref_tp
|}

let tapl_defs_labels =
  {|
%sort nat
%term z nat
%term s {_ nat} nat

%sort label
%name label L
%term lbl {_ nat} label
|}

let tapl_defs_exp =
  {|
%sort ref_exp
%name ref_exp E
%term ref_app {_ ref_exp} {_ ref_exp} ref_exp
%term ref_lam {_ ref_tp} {_ {_ ref_exp} ref_exp} ref_exp
%term dot ref_exp
%term alloc {_ ref_exp} ref_exp
%term deref {_ ref_exp} ref_exp
%term gets {_ ref_exp} {_ ref_exp} ref_exp
%term loc {_ label} ref_exp
|}

let tapl_defs_value =
  {|
%sort ref_value {_ ref_exp}
%name ref_value V
%mode ref_value %in
%term v_lam {{T E}} ref_value (ref_lam T E)
%term v_dot ref_value dot
%term v_loc {{L}} ref_value (loc L)
|}

let tapl_defs_store =
  {|
%sort ref_store
%name ref_store S
%term store_nil ref_store
%term store_cons {_ ref_tp} {_ ref_store} ref_store

%sort length_store {_ ref_store} {_ nat}
%mode length_store %in %out
%term length_store_nil length_store store_nil z
%term length_store_cons {S ref_store} {N nat} %if (length_store (store_cons _ S) (s N)) %<- (length_store S N)
%worlds () (length_store _ _)
%total S (length_store S _)

%sort find_in_store {_ label} {_ ref_store} {_ ref_tp}
%mode find_in_store %in %in %out
%term find_in_store_yes {T ref_tp} find_in_store (lbl z) (store_cons T _) T
%term find_in_store_no {N nat} {S ref_store} {T ref_tp} %if (find_in_store (lbl (s N)) (store_cons _ S) T) %<- (find_in_store (lbl N) S T)
%worlds () (find_in_store _ _ _)
|}

let tapl_defs_heap =
  {|
%sort ref_heap
%name ref_heap H
%term heap_nil ref_heap
%term heap_cons {_ ref_exp} {_ ref_heap} ref_heap

%sort length_heap {_ ref_heap} {_ nat}
%mode length_heap %in %out
%term length_heap_nil length_heap heap_nil z
%term length_heap_cons {H ref_heap} {N nat} %if (length_heap (heap_cons _ H) (s N)) %<- (length_heap H N)
%worlds () (length_heap _ _)
%total H (length_heap H _)

%sort find_in_heap {_ label} {_ ref_heap} {_ ref_exp}
%mode find_in_heap %in %in %out
%term find_in_heap_yes {E ref_exp} find_in_heap (lbl z) (heap_cons E _) E
%term find_in_heap_no {N nat} {H ref_heap} {E ref_exp} %if (find_in_heap (lbl (s N)) (heap_cons _ H) E) %<- (find_in_heap (lbl N) H E)
%worlds () (find_in_heap _ _ _)

%sort replace_in_heap {_ ref_heap} {_ label} {_ ref_exp} {_ ref_heap}
%mode replace_in_heap %in %in %in %out
%term replace_in_heap_yes {E1 ref_exp} {H ref_heap} {E2 ref_exp} replace_in_heap (heap_cons E1 H) (lbl z) E2 (heap_cons E2 H)
%term replace_in_heap_no {E1 ref_exp} {H ref_heap} {N nat} {E2 ref_exp} {H' ref_heap} %if (replace_in_heap (heap_cons E1 H) (lbl (s N)) E2 (heap_cons E1 H')) %<- (replace_in_heap H (lbl N) E2 H')
%worlds () (replace_in_heap _ _ _ _)

%sort append_heap {_ ref_heap} {_ ref_exp} {_ ref_heap}
%mode append_heap %in %in %out
%term append_heap_nil {E ref_exp} append_heap heap_nil E (heap_cons E heap_nil)
%term append_heap_cons {E1 ref_exp} {H ref_heap} {E2 ref_exp} {H' ref_heap} %if (append_heap (heap_cons E1 H) E2 (heap_cons E1 H')) %<- (append_heap H E2 H')
%worlds () (append_heap _ _ _)
%total H (append_heap H _ _)
|}
