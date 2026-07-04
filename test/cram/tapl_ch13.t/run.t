  $ stelf check stelf.toml
  note: %sort nat
  note: %term z  nat
  note: %term s  {_0 nat} nat
  note: %sort nat_eq {_0 nat} {_1 nat}
  note: %term neq_eq_refl  {N nat} nat_eq N N
  note: %sort nat_neq {_0 nat} {_1 nat}
  note: %term nat_neq_zs  {N nat} nat_neq z (s N)
  note: %term nat_neq_sz  {N nat} nat_neq (s N) z
  note: %term nat_neq_ss  {N1 nat} {N2 nat} {_0 nat_neq N1 N2} nat_neq (s N1) (s N2)
  note: %sort nat_lt {_0 nat} {_1 nat}
  note: %term nat_lt_zs  {N nat} nat_lt z (s N)
  note: %term nat_lt_ss  {N1 nat} {N2 nat} {_0 nat_lt N1 N2} nat_lt (s N1) (s N2)
  note: %sort tp
  note: %term =>  {_0 tp} {_1 tp} tp
  note: %term unit  tp
  note: %term ref  {_0 tp} tp
  note: %sort label
  note: %term lbl  {_0 nat} label
  note: %sort exp
  note: %term @  {_0 exp} {_1 exp} exp
  note: %term lam  {_0 tp} {_1 {_1 exp} exp} exp
  note: %term dot  exp
  note: %term alloc  {_0 exp} exp
  note: %term deref  {_0 exp} exp
  note: %term gets  {_0 exp} {_1 exp} exp
  note: %term loc  {_0 label} exp
  note: %sort value {_0 exp}
  note: %term v_lam  {T tp} {E {_0 exp} exp} value (lam T ([_0 exp] E _0))
  note: %term v_dot  value dot
  note: %term v_loc  {L label} value (loc L)
  note: %sort store
  note: %term store_nil  store
  note: %term store_cons  {_0 tp} {_1 store} store
  note: %sort length_store {_0 store} {_1 nat}
  note: %term length_store_nil  length_store store_nil z
  note: %term length_store_cons 
     {S store} {N nat} {T tp} {_0 length_store S N}
        length_store (store_cons T S) (s N)
  => unique: expected a type family name
  
  note: %sort find_in_store {_0 label} {_1 store} {_2 tp}
  note: %term find_in_store_yes 
     {T tp} {S store} find_in_store (lbl z) (store_cons T S) T
  note: %term find_in_store_no 
     {N nat} {S store} {T2 tp} {T1 tp} {_0 find_in_store (lbl N) S T2}
        find_in_store (lbl (s N)) (store_cons T1 S) T2
  => unique: expected a type family name
  
  note: %sort store_extends {_0 store} {_1 store}
  note: %term store_extends_base  {S store} store_extends store_nil S
  note: %term store_extends_ind 
     {S1 store} {S2 store} {T tp} {_0 store_extends S1 S2}
        store_extends (store_cons T S1) (store_cons T S2)
  note: %sort append_store {_0 store} {_1 tp} {_2 store}
  note: %term append_store_nil  {T tp} append_store store_nil T (store_cons T store_nil)
  note: %term append_store_cons 
     {S store} {T2 tp} {S' store} {T1 tp} {_0 append_store S T2 S'}
        append_store (store_cons T1 S) T2 (store_cons T1 S')
  => unique: expected a type family name
  
  note: %sort var {_0 exp} {_1 tp}
  note: %sort of {_0 store} {_1 exp} {_2 tp}
  note: %term t_var  {E exp} {T tp} {S store} {_0 var E T} of S E T
  note: %term t_abs 
     {_ exp} {T1 tp} {S store} {E {_0 exp} exp} {T2 tp}
        {_0 {_0 var _ T1} of S (E _) T2} of S (lam T1 ([_1 exp] E _1)) (T1 => T2)
  note: %term t_app 
     {S store} {E2 exp} {T1 tp} {E1 exp} {T2 tp} {_0 of S E2 T1}
        {_1 of S E1 (T1 => T2)} of S (E1 @ E2) T2
  note: %term t_unit  {S store} of S dot unit
  note: %term t_loc 
     {L label} {S store} {T tp} {_0 find_in_store L S T} of S (loc L) (ref T)
  note: %term t_ref  {S store} {E exp} {T tp} {_0 of S E T} of S (alloc E) (ref T)
  note: %term t_deref  {S store} {E exp} {T tp} {_0 of S E (ref T)} of S (deref E) T
  note: %term t_assign 
     {S store} {E2 exp} {T tp} {E1 exp} {_0 of S E2 T} {_1 of S E1 (ref T)}
        of S (gets E1 E2) unit
  note: %sort heap
  note: %term heap_nil  heap
  note: %term heap_cons  {_0 exp} {_1 heap} heap
  note: %sort length_heap {_0 heap} {_1 nat}
  note: %term length_heap_nil  length_heap heap_nil z
  note: %term length_heap_cons 
     {H heap} {N nat} {E exp} {_0 length_heap H N}
        length_heap (heap_cons E H) (s N)
  => unique: expected a type family name
  
  note: %sort find_in_heap {_0 label} {_1 heap} {_2 exp}
  note: %term find_in_heap_yes  {E exp} {H heap} find_in_heap (lbl z) (heap_cons E H) E
  note: %term find_in_heap_no 
     {N nat} {H heap} {E' exp} {E exp} {_0 find_in_heap (lbl N) H E'}
        find_in_heap (lbl (s N)) (heap_cons E H) E'
  => unique: expected a type family name
  
  note: %sort replace_in_heap {_0 heap} {_1 label} {_2 exp} {_3 heap}
  note: %term replace_in_heap_yes 
     {E1 exp} {H heap} {E2 exp}
        replace_in_heap (heap_cons E1 H) (lbl z) E2 (heap_cons E2 H)
  note: %term replace_in_heap_no 
     {H heap} {N nat} {E2 exp} {H' heap} {E1 exp}
        {_0 replace_in_heap H (lbl N) E2 H'}
        replace_in_heap (heap_cons E1 H) (lbl (s N)) E2 (heap_cons E1 H')
  => unique: expected a type family name
  
  note: %sort append_heap {_0 heap} {_1 exp} {_2 heap}
  note: %term append_heap_nil  {E exp} append_heap heap_nil E (heap_cons E heap_nil)
  note: %term append_heap_cons 
     {H heap} {E2 exp} {H' heap} {E1 exp} {_0 append_heap H E2 H'}
        append_heap (heap_cons E1 H) E2 (heap_cons E1 H')
  => unique: expected a type family name
  
  note: %sort check_wt {_0 store} {_1 store} {_2 heap}
  note: %term check_wt_nil  {S store} check_wt S store_nil heap_nil
  note: %term check_wt_cons 
     {S1 store} {S2 store} {H heap} {E exp} {T tp} {_0 check_wt S1 S2 H}
        {_1 of S1 E T} check_wt S1 (store_cons T S2) (heap_cons E H)
  note: %sort wt_heap {_0 store} {_1 heap}
  note: %term wt_heap_def  {S store} {H heap} {_0 check_wt S S H} wt_heap S H
  note: %sort step {_0 heap} {_1 exp} {_2 heap} {_3 exp}
  note: %term e_app1 
     {H heap} {E1 exp} {H' heap} {E1' exp} {E2 exp} {_0 step H E1 H' E1'}
        step H (E1 @ E2) H' (E1' @ E2)
  note: %term e_app2 
     {H heap} {E2 exp} {H' heap} {E2' exp} {E1 exp} {_0 step H E2 H' E2'}
        {_1 value E1} step H (E1 @ E2) H' (E1 @ E2')
  note: %term e_alloc 
     {H heap} {E exp} {H' heap} {E' exp} {_0 step H E H' E'}
        step H (alloc E) H' (alloc E')
  note: %term e_deref 
     {H heap} {E exp} {H' heap} {E' exp} {_0 step H E H' E'}
        step H (deref E) H' (deref E')
  note: %term e_gets1 
     {H heap} {E1 exp} {H' heap} {E1' exp} {E2 exp} {_0 step H E1 H' E1'}
        step H (gets E1 E2) H' (gets E1' E2)
  note: %term e_gets2 
     {H heap} {E2 exp} {H' heap} {E2' exp} {E1 exp} {_0 step H E2 H' E2'}
        {_1 value E1} step H (gets E1 E2) H' (gets E1 E2')
  note: %term e_appabs 
     {E2 exp} {H heap} {T tp} {E1 {_0 exp} exp} {_0 value E2}
        step H (lam T ([_1 exp] E1 _1) @ E2) H (E1 E2)
  note: %term e_allocVal 
     {H heap} {N' nat} {E exp} {H' heap} {_0 length_heap H N'}
        {_1 append_heap H E H'} {_2 value E} step H (alloc E) H' (loc (lbl N'))
  note: %term e_derefVal 
     {L label} {H heap} {E exp} {_0 find_in_heap L H E} step H (deref (loc L)) H E
  note: %term e_getsVal 
     {H heap} {L label} {E exp} {H' heap} {_0 replace_in_heap H L E H'}
        {_1 value E} step H (gets (loc L) E) H' dot

