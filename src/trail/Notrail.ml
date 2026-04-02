(* # 1 "src/trail/Notrail.sig.ml" *)

(* # 1 "src/trail/Notrail.fun.ml" *)

(* # 1 "src/trail/Notrail.sml.ml" *)
open Basis
open Trail_

(* Not Trailing Abstract Operations *)
(* Author: Roberto Virga *)
module NoTrail : TRAIL = struct
  type 'a trail = unit

  let trail () = ()
  let suspend ((), _copy) = ()
  let resume ((), (), _reset) = ()
  let reset () = ()
  let mark () = ()
  let unwind ((), _undo) = ()
  let log ((), _action) = ()
end
(* structure NoTrail *)
