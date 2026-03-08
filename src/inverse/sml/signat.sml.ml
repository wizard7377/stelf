open! Basis

module type SIGNAT = sig
  type nonrec key
  type nonrec 'a sgn

  exception Signat of string

  val empty : unit -> 'a sgn
  val insert : 'a sgn -> key * 'a -> 'a sgn

  (* raises Signat if key is not fresh*)
  val lookup : 'a sgn -> key -> 'a

  (* raises Signat if not present *)
  val size : 'a sgn -> int
end

module ListSignat : SIGNAT = struct
  module L = Lib

  type nonrec key = int
  type nonrec 'a sgn = (key * 'a) list

  exception Signat of string

  let rec empty () = []

  let rec insert sgn ((k, a) as p) =
    begin if L.exists (function k', _ -> k = k') sgn then
      raise (Signat "insert: signat contains key")
    else p :: sgn
    end

  let rec lookup sgn x =
    begin match L.assoc x sgn with
    | Some y -> y
    | None -> raise (Signat "lookup: no such key")
    end

  let rec size l = length l
end

module GrowarraySignat : SIGNAT = struct
  module L = Lib
  module G = GrowArray

  type nonrec key = int
  type nonrec 'a __0 = { arr : 'a G.growarray; size : int ref }
  type nonrec 'a sgn = 'a __0

  exception Signat of string

  let size = ref 0
  let rec empty () = { arr = G.empty (); size = ref 0 }

  let rec insert (sgn : 'a sgn) (n, v) =
    begin if G.length ((fun r -> r.arr) sgn) > n then
      raise (Signat "insert: signat contains key")
    else begin
      G.update ((fun r -> r.arr) sgn) n v;
      begin
        begin if n > !((fun r -> r.size) sgn) then (fun r -> r.size) sgn := n
        else ()
        end;
        sgn
      end
    end
    end

  let rec lookup (sgn : 'a sgn) n = G.sub ((fun r -> r.arr) sgn) n
  let rec size (sgn : 'a sgn) = !((fun r -> r.size) sgn)
end

module Signat = GrowarraySignat
