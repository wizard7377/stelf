module Pos = Pos

type tag 



val of_pos : start:Pos.pos -> finish:Pos.pos -> tag
val of_range : Pos.range -> tag
val better : tag -> tag -> [ `Disjoint | `Better | `Worse ] 
