(* # 1 "src/table/Queue.sig.ml" *)

open Basis

(* Queues *)
(* Author: Frank Pfenning *)
include Queue_intf
(* signature QUEUE *)

(* # 1 "src/table/Queue.fun.ml" *)

(* # 1 "src/table/Queue.sml.ml" *)

(* Queues *)
(* Author: Frank Pfenning *)
(* Standard functional implementation of queues *)
(*
   Since in the typical use `delete' is not of constant amortized time we
   provide a special `toList' operation which permits constant
   amortized access under programmer control.
*)
module Queue : QUEUE = struct
  (* Representation invariant:
     If  q = (inp, out)  then  q == out @ rev(inp)
  *)
  type 'a queue = 'a list * 'a list

  let empty = ([], [])
  let insert (x, (inp, out)) = (x :: inp, out)

  let rec delete = function
    | [], [] -> None
    | inp, x :: out -> Some (x, (inp, out))
    | inp, [] -> delete ([], List.rev inp)

  let insertFront (x, (inp, out)) = (inp, x :: out)

  let deleteEnd = function
    | [], [] -> None
    | x :: inp, out -> Some (x, (inp, out))
    | [], out -> delete (List.rev out, [])

  (* toList q ==> (l, NONE)  means q == l and toList is constant time *)
  (* toList q ==> (l, SOME(q')) means q == l == q' *)
  (* and toList q' is constant time *)
  let toList = function
    | [], out -> (out, None)
    | inp, out ->
        let out' = out @ List.rev inp in
        (out', Some ([], out'))
end
(* structure Queue *)
