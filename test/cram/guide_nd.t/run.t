  $ stelf check stelf.toml
  note: %sort i
  note: %sort o
  note: %term imp  {_0 o} {_1 o} o
  note: %term and  {_0 o} {_1 o} o
  note: %term true  o
  note: %term or  {_0 o} {_1 o} o
  note: %term false  o
  note: %term forall  {_0 {_0 i} o} o
  note: %term exists  {_0 {_0 i} o} o
  note: %sort nd {_0 o}
  note: %term impi  {A o} {B o} {_0 {_0 nd A} nd B} nd (A imp B)
  note: %term impe  {A o} {B o} {_0 nd A} {_1 nd (A imp B)} nd B
  note: %term andi  {B o} {A o} {_0 nd B} {_1 nd A} nd (A and B)
  note: %term ande1  {A o} {B o} {_0 nd (A and B)} nd A
  note: %term ande2  {A o} {B o} {_0 nd (A and B)} nd B
  note: %term truei  nd true
  note: %term ori1  {A o} {B o} {_0 nd A} nd (A or B)
  note: %term ori2  {B o} {A o} {_0 nd B} nd (A or B)
  note: %term ore 
     {B o} {C o} {A o} {_0 {_0 nd B} nd C} {_1 {_1 nd A} nd C} {_2 nd (A or B)}
        nd C
  note: %term falsee  {C o} {_0 nd false} nd C
  note: %term foralli  {A {_0 i} o} {_ i} {_0 {_0 i} nd (A _)} nd (forall ([_1 i] A _1))
  note: %term foralle  {A {_0 i} o} {T i} {_0 nd (forall ([_0 i] A _0))} nd (A T)
  note: %term existsi  {A {_0 i} o} {T i} {_0 nd (A T)} nd (exists ([_1 i] A _1))
  note: %term existse 
     {A {_0 i} o} {_ i} {C o} {_0 {_0 i} {_1 nd (A _)} nd C}
        {_1 nd (exists ([_1 i] A _1))} nd C
  note: %sort red {A o} {_0 nd A} {_1 nd A}

