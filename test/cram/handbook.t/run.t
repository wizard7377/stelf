  $ stelf check main.lf
  note: %sort i
  note: %sort o
  note: %term imp  {_0 o} {_1 o} o
  note: %term not  {_0 o} o
  note: %term forall  {_0 {_0 i} o} o
  note: %sort nd {_0 o}
  note: %term impi  {A o} {B o} {_0 {_0 nd A} nd B} nd (A imp B)
  note: %term impe  {A o} {B o} {_0 nd A} {_1 nd (A imp B)} nd B
  note: %term noti  {A o} {_ o} {_0 {_0 o} {_1 nd A} nd _} nd (not A)
  note: %term note  {A o} {C o} {_0 nd A} {_1 nd (not A)} nd C
  note: %term foralli  {A {_0 i} o} {_ i} {_0 {_0 i} nd (A _)} nd (forall ([_1 i] A _1))
  note: %term foralle  {A {_0 i} o} {T i} {_0 nd (forall ([_0 i] A _0))} nd (A T)
  note: %sort hil {_0 o}
  note: %term k  {A o} {B o} hil (A imp B imp A)
  note: %term s  {A o} {B o} {C o} hil ((A imp B imp C) imp (A imp B) imp A imp C)
  note: %term n1  {A o} {B o} hil ((A imp not B) imp (A imp B) imp not A)
  note: %term n2  {A o} {_ o} hil (not A imp A imp _)
  note: %term f1  {A {_0 i} o} {T i} hil (forall ([_0 i] A _0) imp A T)
  note: %term f2 
     {B o} {A {_0 i} o}
        hil (forall ([x i] B imp A x) imp B imp forall ([_0 i] A _0))
  note: %term mp  {A o} {B o} {_0 hil A} {_1 hil (A imp B)} hil B
  note: %term ug  {A {_0 i} o} {_ i} {_0 {_0 i} hil (A _)} hil (forall ([_1 i] A _1))
  note: %sort hilnd {_ o} {_0 hil _} {_1 nd _}
  note: %term hnd_k  {_?1 o} {_?2 o} hilnd k (impi ([u nd _?1] impi ([v nd _?2] u)))
  note: main.lf:1.1-1.1 Error: 
  Type mismatch
  Expected: nd (_?1 imp _?2)
  Inferred: nd _?1
  Variable occurrence
  Argument type did not match function domain type
  (Index object(s) did not match)
  warning: Type mismatch
  Expected: nd (_?1 imp _?2)
  Inferred: nd _?1
  Variable occurrence
  Argument type did not match function domain type
  (Index object(s) did not match)note: main.lf:1.1-1.1 Error: 
  Type mismatch
  Expected: nd ((_?4 imp _?5 imp _?6) imp (_?4 imp _?5) imp _?4 imp _?6)
  Inferred: nd (_?3 imp _?3 imp (_?3 imp _?1) imp _?2)
  Variable occurrence
  Argument type did not match function domain type
  (Index object(s) did not match)
  warning: Type mismatch
  Expected: nd ((_?4 imp _?5 imp _?6) imp (_?4 imp _?5) imp _?4 imp _?6)
  Inferred: nd (_?3 imp _?3 imp (_?3 imp _?1) imp _?2)
  Variable occurrence
  Argument type did not match function domain type
  (Index object(s) did not match)error: [recon] 1.1623-1.1629 Error: 
   2 errors found
  [1]

