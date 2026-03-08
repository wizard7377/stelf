open! Basis

(* Stream Library *)
(* Author: Frank Pfenning *)
(* BASIC_STREAM defines the visible ""core"" of streams *)
module type BASIC_STREAM = sig
  type nonrec 'a stream
  type 'a front = Empty | Cons of 'a * 'a stream

  (* Lazy stream construction and exposure *)
  val delay : (unit -> 'a front) -> 'a stream
  val expose : 'a stream -> 'a front

  (* Eager stream construction *)
  val empty : 'a stream
  val cons : 'a * 'a stream -> 'a stream
end

module BasicStream : BASIC_STREAM = struct
  type 'a stream = Stream of (unit -> 'a front)
  and 'a front = Empty | Cons of 'a * 'a stream

  let rec delay d = Stream d
  let rec expose (Stream d) = d ()
  let empty = Stream (function () -> Empty)
  let rec cons (x, s) = Stream (function () -> Cons (x, s))
end

(* Note that this implementation is NOT semantically *)
(* equivalent to the plain (non-memoizing) streams, since *)
(* effects will be executed only once in this implementation *)
module BasicMemoStream : BASIC_STREAM = struct
  type 'a stream = Stream of (unit -> 'a front)
  and 'a front = Empty | Cons of 'a * 'a stream

  exception Uninitialized

  let rec expose (Stream d) = d ()

  let rec delay d =
    let memo = ref (function () -> raise Uninitialized) in
    let rec memoFun () =
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
  let rec cons (x, s) = Stream (function () -> Cons (x, s))
end

(* STREAM extends BASIC_STREAMS by operations *)
(* definable without reference to the implementation *)
module type STREAM = sig
  include BASIC_STREAM

  exception EmptyStream

  val null : 'a stream -> bool
  val hd : 'a stream -> 'a
  val tl : 'a stream -> 'a stream
  val map : ('a -> 'b) -> 'a stream -> 'b stream
  val filter : ('a -> bool) -> 'a stream -> 'a stream
  val exists : ('a -> bool) -> 'a stream -> bool
  val take : 'a stream * int -> 'a list
  val drop : 'a stream * int -> 'a stream
  val fromList : 'a list -> 'a stream
  val toList : 'a stream -> 'a list
  val tabulate : (int -> 'a) -> 'a stream
end

module MakeStream (Stream__0 : sig
  module BasicStream : BASIC_STREAM
end) : STREAM = struct
  include Stream__0.BasicStream

  exception EmptyStream

  (* functions null, hd, tl, map, filter, exists, take, drop *)
  (* parallel the functions in the List structure *)
  let rec null s = null' (expose s)
  and null' = function Empty -> true | Cons _ -> false

  let rec hd s = hd' (expose s)
  and hd' = function Empty -> raise EmptyStream | Cons (x, s) -> x

  let rec tl s = tl' (expose s)
  and tl' = function Empty -> raise EmptyStream | Cons (x, s) -> s

  let rec map f s = delay (function () -> map' f (expose s))

  and map' arg__1 arg__2 =
    begin match (arg__1, arg__2) with
    | f, Empty -> Empty
    | f, Cons (x, s) -> Cons (f x, map f s)
    end

  let rec filter p s = delay (function () -> filter' p (expose s))

  and filter' arg__3 arg__4 =
    begin match (arg__3, arg__4) with
    | p, Empty -> Empty
    | p, Cons (x, s) -> begin
        if p x then Cons (x, filter p s) else filter' p (expose s)
      end
    end

  let rec exists p s = exists' p (expose s)

  and exists' arg__5 arg__6 =
    begin match (arg__5, arg__6) with
    | p, Empty -> false
    | p, Cons (x, s) -> p x || exists p s
    end

  let rec takePos = function s, 0 -> [] | s, n -> take' (expose s, n)

  and take' = function
    | Empty, _ -> []
    | Cons (x, s), n -> x :: takePos (s, n - 1)

  let rec take (s, n) =
    begin if n < 0 then raise Subscript else takePos (s, n)
    end

  let rec fromList = function [] -> empty | x :: l -> cons (x, fromList l)

  let rec toList s = toList' (expose s)
  and toList' = function Empty -> [] | Cons (x, s) -> x :: toList s

  let rec dropPos = function s, 0 -> s | s, n -> drop' (expose s, n)
  and drop' = function Empty, _ -> empty | Cons (x, s), n -> dropPos (s, n - 1)

  let rec drop (s, n) =
    begin if n < 0 then raise Subscript else dropPos (s, n)
    end

  let rec tabulate f = delay (function () -> tabulate' f)
  and tabulate' f = Cons (f 0, tabulate (function i -> f (i + 1)))
end

(* structure Stream :> STREAM --- non-memoizing *)
module Stream : STREAM = MakeStream (struct
  module BasicStream = BasicStream
end)

(* structure MStream :> STREAM --- memoizing *)
module MStream : STREAM = MakeStream (struct
  module BasicStream = BasicMemoStream
end)
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
