(* # 1 "src/trail/trail_.sig.ml" *)
open! Basis

(* Trailing Abstract Operations *)
(* Author: Roberto Virga *)
module type TRAIL = sig
  type nonrec 'a trail

  val trail : unit -> 'a trail
  val suspend : 'a trail * ('a -> 'b) -> 'b trail
  val resume : 'b trail * 'a trail * ('b -> 'a) -> unit
  val reset : 'a trail -> unit
  val mark : 'a trail -> unit
  val unwind : 'a trail * ('a -> unit) -> unit
  val log : 'a trail * 'a -> unit
end
(* signature TRAIL *)

(* # 1 "src/trail/trail_.fun.ml" *)

(* # 1 "src/trail/trail_.sml.ml" *)
open! Basis

(* Trailing Abstract Operations *)
(* Author: Roberto Virga *)
module Trail : TRAIL = struct
  type 'a trail_ = Cons of 'a * 'a trail_ | Mark of 'a trail_ | Nil
  type nonrec 'a trail = 'a trail_ ref

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
