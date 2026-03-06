# 1 "src/trail/notrail.sig.ml"

# 1 "src/trail/notrail.fun.ml"

# 1 "src/trail/notrail.sml.ml"
open! Basis;;
(* Not Trailing Abstract Operations *);;
(* Author: Roberto Virga *);;
module NoTrail : TRAIL =
  struct
    type nonrec 'a trail = unit;;
    let rec trail () = ();;
    let rec suspend ((), copy) = ();;
    let rec resume ((), (), reset) = ();;
    let rec reset () = ();;
    let rec mark () = ();;
    let rec unwind ((), undo) = ();;
    let rec log ((), action) = ();;
    end;;
(* structure NoTrail *);;