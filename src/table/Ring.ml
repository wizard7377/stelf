(* # 1 "src/table/Ring.sig.ml" *)

(** Cyclic list (ring) operations and traversal helpers. *)

open Basis

(* Rings (aka cyclic lists) *)
(* Author: Carsten Schuermann *)
include Ring_intf
(* does not necessarily map f in order *)
(* signature RING *)

(* # 1 "src/table/Ring.fun.ml" *)

(* # 1 "src/table/Ring.sml.ml" *)

(* Rings (aka cyclic lists) *)
(* Author: Carsten Schuermann *)
module Ring : RING = struct
  exception Empty

  type 'a ring = 'a list * 'a list

  (* Representation Invariant:  
     ([an,...,ai+1], [a1,...,ai]) represents
     [a1,...,ai,ai+1,...,an] wrapping around
  *)
  (* empty q = true if q = [], false otherwise *)
  let empty (r, l) = (r, l) = ([], [])

  (* init l = l (as ring) *)
  let init l = ([], l)

  (* insert ([], x) = [x]
     insert ([a1, a2 ... an], x) = [x, a1, a2, ... an]
  *)
  let insert ((r, l), y) = (r, y :: l)

  (* current [] = raise Empty
     current [a1, a2 ... an] = a1
  *)
  let rec current = function
    | [], [] -> raise Empty
    | _, x :: _ -> x
    | l, [] -> current ([], rev l)

  (* next [] = raise Empty
     next [a1, a2 ... an]) = [a2 ... an, a1]
  *)
  let rec next = function
    | [], [] -> raise Empty
    | r, [] -> next ([], rev r)
    | r, x :: l -> (x :: r, l)

  (* previous [] = ERROR
     previous [a1, a2 ... an]) = [a2 ... an, a1]
  *)
  let rec previous = function
    | [], [] -> raise Empty
    | [], l -> previous (rev l, [])
    | x :: r, l -> (r, x :: l)

  (* delete [] = raise Empty
     delete [a1, a2 ... an] = [a2 ... an]
  *)
  let rec delete = function
    | [], [] -> raise Empty
    | r, [] -> delete ([], rev r)
    | r, _x :: l -> (r, l)

  (* foldr is inefficient *)
  let foldr f i (r, l) = List.foldr f i (l @ rev r)

  (* order of map is undefined.  relevant? *)
  let map f (r, l) = (List.map f r, List.map f l)
end
(* structure Ring *)
