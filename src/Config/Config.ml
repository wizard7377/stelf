module type CONFIG = CONFIG.CONFIG 
module Default_Config () : CONFIG = struct 
  open CONFIG
  open Flag
  type 'a t = Parser of 'a parser | Solver of 'a solver | Display of 'a display
  let global : 'a . (('a t -> 'a) ref) = assert false
  let get c = !global c
  let set c v =  global := (fun c' -> if c' = c then v else !global c')
end

module Copy_Config = functor (C : CONFIG) -> struct 
  include C
  type 'a t = 'a C.t
  let copy c = assert false
end   