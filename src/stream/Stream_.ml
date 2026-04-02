(* # 1 "src/stream/Stream_.sig.ml" *)

(* # 1 "src/stream/Stream_.fun.ml" *)

(* # 1 "src/stream/Stream_.sml.ml" *)

open Basis

(* Stream Library *)
(* Author: Frank Pfenning *)
(* BASIC_STREAM defines the visible ""core"" of streams *)
include Stream_intf
module BasicStream : BASIC_STREAM = struct
  type 'a stream = Stream of (unit -> 'a front)
  and 'a front = Empty | Cons of 'a * 'a stream

  let delay d = Stream d
  let expose (Stream d) = d ()
  let empty = Stream (function () -> Empty)
  let cons (x, s) = Stream (function () -> Cons (x, s))
end

(* Note that this implementation is NOT semantically *)
(* equivalent to the plain (non-memoizing) streams, since *)
(* effects will be executed only once in this implementation *)
module BasicMemoStream : BASIC_STREAM = struct
  type 'a stream = Stream of (unit -> 'a front)
  and 'a front = Empty | Cons of 'a * 'a stream

  exception Uninitialized

  let expose (Stream d) = d ()

  let delay d =
    let memo = ref (function () -> raise Uninitialized) in
    let memoFun () =
      try
        let r = d () in
        begin
          (memo := function () -> r);
          r
        end
      with exn ->
        begin
          (memo := function () -> raise exn);
          raise exn
        end
    in
    begin
      memo := memoFun;
      Stream (function () -> !memo ())
    end

  let empty = Stream (function () -> Empty)
  let cons (x, s) = Stream (function () -> Cons (x, s))
end

(* STREAM extends BASIC_STREAMS by operations *)
(* definable without reference to the implementation *)
module MakeStream (BasicStream : BASIC_STREAM) : STREAM = struct
  include BasicStream

  exception EmptyStream

  (* functions null, hd, tl, map, filter, exists, take, drop *)
  (* parallel the functions in the List structure *)
  let rec null s = null' (expose s)
  and null' = function Empty -> true | Cons _ -> false

  let rec hd s = hd' (expose s)
  and hd' = function Empty -> raise EmptyStream | Cons (x, _s) -> x

  let rec tl s = tl' (expose s)
  and tl' = function Empty -> raise EmptyStream | Cons (_x, s) -> s

  let rec map f s = delay (function () -> map' f (expose s))

  and map' arg__1 arg__2 =
    begin match (arg__1, arg__2) with
    | _f, Empty -> Empty
    | f, Cons (x, s) -> Cons (f x, map f s)
    end

  let rec filter p s = delay (function () -> filter' p (expose s))

  and filter' arg__3 arg__4 =
    begin match (arg__3, arg__4) with
    | _p, Empty -> Empty
    | p, Cons (x, s) -> begin
        if p x then Cons (x, filter p s) else filter' p (expose s)
      end
    end

  let rec exists p s = exists' p (expose s)

  and exists' arg__5 arg__6 =
    begin match (arg__5, arg__6) with
    | _p, Empty -> false
    | p, Cons (x, s) -> p x || exists p s
    end

  let rec takePos = function _s, 0 -> [] | s, n -> take' (expose s, n)

  and take' = function
    | Empty, _ -> []
    | Cons (x, s), n -> x :: takePos (s, n - 1)

  let take (s, n) =
    begin if n < 0 then raise Subscript else takePos (s, n)
    end

  let rec fromList = function [] -> empty | x :: l -> cons (x, fromList l)

  let rec toList s = toList' (expose s)
  and toList' = function Empty -> [] | Cons (x, s) -> x :: toList s

  let rec dropPos = function s, 0 -> s | s, n -> drop' (expose s, n)

  and drop' = function
    | Empty, _ -> empty
    | Cons (_x, s), n -> dropPos (s, n - 1)

  let drop (s, n) =
    begin if n < 0 then raise Subscript else dropPos (s, n)
    end

  let rec tabulate f = delay (function () -> tabulate' f)
  and tabulate' f = Cons (f 0, tabulate (function i -> f (i + 1)))
end

(* structure Stream :> STREAM --- non-memoizing *)
module Stream : STREAM = MakeStream (BasicStream)

(* structure MStream :> STREAM --- memoizing *)
module MStream : STREAM = MakeStream (BasicMemoStream)
(*
structure S = Stream;   abbreviation 

 simple definition 
fun ones' () = S.Cons(1, S.delay ones');
val ones = S.delay ones';

 alternative definitions 
val ones = S.tabulate (fn _ => 1);
val nats = S.tabulate (fn i => i);
val poss = S.map (fn i => i+1) nats;
val evens = S.map (fn i => 2*i) nats;

 notMultiple p q >=> true iff q is not a multiple of p 
fun notMultiple p q = (q mod p <> 0);

fun sieve s = S.delay (fn () => sieve' (S.expose s))
and sieve' (S.Empty) = S.Empty
  | sieve' (S.Cons(p, s)) =
      S.Cons (p, sieve (S.filter (notMultiple p) s));

val primes = sieve (S.tabulate (fn i => i+2));
*)
