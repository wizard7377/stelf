(* # 1 "src/table/ring.sig.ml" *)
open! Basis

(* Rings (aka cyclic lists) *)
(* Author: Carsten Schuermann *)
module type RING = sig
  exception Empty

  type nonrec 'a ring

  val init : 'a list -> 'a ring
  val empty : 'a ring -> bool
  val insert : 'a ring * 'a -> 'a ring
  val delete : 'a ring -> 'a ring
  val current : 'a ring -> 'a
  val next : 'a ring -> 'a ring
  val previous : 'a ring -> 'a ring
  val foldr : ('a * 'b -> 'b) -> 'b -> 'a ring -> 'b
  val map : ('a -> 'b) -> 'a ring -> 'b ring
end

(* does not necessarily map f in order *)
(* signature RING *)

(* # 1 "src/table/ring.fun.ml" *)

(* # 1 "src/table/ring.sml.ml" *)
open! Basis

(* Rings (aka cyclic lists) *)
(* Author: Carsten Schuermann *)
module Ring : RING = struct
  exception Empty

  type nonrec 'a ring = 'a list * 'a list

  (* Representation Invariant:  
     ([an,...,ai+1], [a1,...,ai]) represents
     [a1,...,ai,ai+1,...,an] wrapping around
  *)
  (* empty q = true if q = [], false otherwise *)
  let empty = function [], [] -> true | _ -> false

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
