
module Pos = Pos 


type tag = FC of Pos.pos * Pos.pos 


let of_pos ~start ~finish = FC (start, finish)
let of_range (start, finish) = FC (start, finish)
let earlier (x : Pos.pos) (y : Pos.pos) = 
  if x.line < y.line then true
  else if x.line > y.line then false
  else x.column < y.column
let better (FC (s1, f1)) (FC (s2, f2)) = 
  if earlier s1 s2 && earlier f2 f1 then `Better
  else if earlier s2 s1 && earlier f1 f2 then `Worse
  else `Disjoint
  