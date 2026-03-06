open! Basis;;
(* Trailing Abstract Operations *);;
(* Author: Roberto Virga *);;
module type TRAIL = sig
                    type nonrec 'a trail
                    val trail : unit -> 'a trail
                    val suspend : ('a trail * ('a -> 'b)) -> 'b trail
                    val resume : ('b trail * 'a trail * ('b -> 'a)) -> unit
                    val reset : 'a trail -> unit
                    val mark : 'a trail -> unit
                    val unwind : ('a trail * ('a -> unit)) -> unit
                    val log : ('a trail * 'a) -> unit
                    end;;
(* signature TRAIL *);;