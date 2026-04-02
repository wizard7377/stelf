(* # 1 "src/trail/Trail_.sig.ml" *)

open Basis

(* Trailing Abstract Operations *)

(** Author: Roberto Virga *)
include Trail_intf
(* signature TRAIL *)

(* # 1 "src/trail/Trail_.fun.ml" *)

(* # 1 "src/trail/Trail_.sml.ml" *)

(* Trailing Abstract Operations *)
(* Author: Roberto Virga *)
module Trail : TRAIL = struct
  type 'a trail_ = Cons of 'a * 'a trail_ | Mark of 'a trail_ | Nil
  type 'a trail = 'a trail_ ref

  let trail () = ref Nil
  let reset trail = trail := Nil

  let suspend (trail, copy) =
    let rec suspend' = function
      | Nil -> Nil
      | Mark trail -> suspend' trail
      | Cons (action, trail) -> Cons (copy action, suspend' trail)
    in
    let ftrail = suspend' !trail in
    ref ftrail

  let resume (ftrail, trail, reset) =
    let rec resume' = function
      | Nil -> Nil
      | Mark ftrail -> resume' ftrail
      | Cons (faction, ftrail) -> Cons (reset faction, resume' ftrail)
    in
    let trail' = resume' !ftrail in
    trail := trail'

  let mark trail = trail := Mark !trail

  let unwind (trail, undo) =
    let rec unwind' = function
      | Nil -> Nil
      | Mark trail -> trail
      | Cons (action, trail) -> begin
          undo action;
          unwind' trail
        end
    in
    trail := unwind' !trail

  let log (trail, action) = trail := Cons (action, !trail)
  (*	  | suspend' (Mark trail) = (Mark (suspend' trail))*)
  (*	  | resume' (Mark ftrail) = (Mark (resume' ftrail)) *)
end
(* local ... *)
(* structure Trail *)
