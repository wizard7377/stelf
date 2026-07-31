let on1 : ('a -> 'r) -> 'a -> 'r = fun f x -> f x
let on2 : (('a * 'b) -> 'a -> 'b -> 'r) = fun f x y -> f (x, y)
let on3 : (('a * 'b * 'c) -> 'r) -> 'a -> 'b -> 'c -> 'r) = fun f x y z -> f (x, y, z)
let on4 : (('a * 'b * 'c * 'd) -> 'r) -> 'a -> 'b -> 'c -> 'd -> 'r = fun f w x y z -> f (w, x, y, z)
