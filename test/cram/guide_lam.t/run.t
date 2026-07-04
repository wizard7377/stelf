  $ stelf check main.lf
  note: %sort tp
  note: %term arrow  {_0 tp} {_1 tp} tp
  note: %sort exp
  note: %term lam  {_0 {_0 exp} exp} exp
  note: %term app  {_0 exp} {_1 exp} exp
  note: %sort of {_0 exp} {_1 tp}
  note: %term tp_lam 
     {_ exp} {T1 tp} {E {_0 exp} exp} {T2 tp} {_0 {_0 of _ T1} of (E _) T2}
        of (lam ([_1 exp] E _1)) (arrow T1 T2)
  note: %term tp_app 
     {E2 exp} {T2 tp} {E1 exp} {T1 tp} {_0 of E2 T2} {_1 of E1 (arrow T2 T1)}
        of (app E1 E2) T1
  note: %sort eval {_0 exp} {_1 exp}
  note: %term ev_lam  {E {_0 exp} exp} eval (lam ([_0 exp] E _0)) (lam ([_0 exp] E _0))
  note: %term ev_app 
     {E1' {_0 exp} exp} {V2 exp} {V exp} {E2 exp} {E1 exp} {_0 eval (E1' V2) V}
        {_1 eval E2 V2} {_2 eval E1 (lam ([_2 exp] E1' _2))} eval (app E1 E2) V

