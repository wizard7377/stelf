(* # 1 "src/domains/rationals.sig.ml" *)
open Basis
open Int_inf
open Int_inf.Int_inf_
open Ordered_field
open Integers

(* Rational numbers *)
(* Author: Roberto Virga *)
module type RATIONALS = sig
  include ORDERED_FIELD
  module Integers : INTEGERS

  (* Conversions between rationals and integers *)
  val fromInteger : Integers.int -> number
  val floor : number -> Integers.int
  val ceiling : number -> Integers.int

  (* Basic projections *)
  val numerator : number -> Integers.int
  val denominator : number -> Integers.int
end
(* signature RATIONALS *)

(* # 1 "src/domains/rationals.fun.ml" *)

(* Rationals *)
(* Author: Roberto Virga *)
module Rationals (Integers : INTEGERS) :
  RATIONALS with type Integers.int = Integers.int = struct
  module Integers = Integers

  let name = "rational"

  exception Div = Div

  module I = Integers

  type number = Fract of Int.int * I.int * I.int

  open! struct
    let zero = Fract (0, I.fromInt 0, I.fromInt 1)
    let one = Fract (1, I.fromInt 1, I.fromInt 1)

    exception Div

    let normalize = function
      | Fract (0, _, _) -> zero
      | Fract (s, n, d) ->
          let rec gcd (m, n) =
            begin if m = I.fromInt 0 then n
            else begin
              if n = I.fromInt 0 then m
              else begin
                if I.( > ) m n then gcd (I.mod_ (m, n), n)
                else gcd (m, I.mod_ (n, m))
              end
            end
            end
          in
          let g = gcd (n, d) in
          Fract (s, I.div (n, g), I.div (d, g))

    let ( ~- ) (Fract (s, n, d)) = Fract (Int.( ~- ) s, n, d)

    let add_ (Fract (s1, n1, d1), Fract (s2, n2, d2)) =
      let n =
        I.( + )
          (I.( * ) (I.( * ) (I.fromInt s1) n1) d2)
          (I.( * ) (I.( * ) (I.fromInt s2) n2) d1)
      in
      normalize (Fract (I.sign n, I.abs n, I.( * ) d1 d2))

    let ( + ) a b = add_ (a, b)

    let sub_ (Fract (s1, n1, d1), Fract (s2, n2, d2)) =
      let n =
        I.( - )
          (I.( * ) (I.( * ) (I.fromInt s1) n1) d2)
          (I.( * ) (I.( * ) (I.fromInt s2) n2) d1)
      in
      normalize (Fract (I.sign n, I.abs n, I.( * ) d1 d2))

    let ( - ) a b = sub_ (a, b)

    let mul_ (Fract (s1, n1, d1), Fract (s2, n2, d2)) =
      normalize (Fract (Int.( * ) s1 s2, I.( * ) n1 n2, I.( * ) d1 d2))

    let ( * ) a b = mul_ (a, b)

    let inverse = function
      | Fract (0, _, _) -> raise Div
      | Fract (s, n, d) -> Fract (s, d, n)

    let sign (Fract (s, _n, _d)) = s
    let numerator (Fract (_s, n, _d)) = n
    let denominator (Fract (_s, _n, d)) = d
    let abs (Fract (s, n, d)) = Fract (Int.abs s, n, d)

    (* Workaround: I.compare returns wrong order path *)
    let compare (Fract (s1, n1, d1), Fract (s2, n2, d2)) =
      let a = I.( * ) (I.( * ) (I.fromInt s1) n1) d2 in
      let b = I.( * ) (I.( * ) (I.fromInt s2) n2) d1 in
      I.compare (a, b)

    let ( > ) q1 q2 = compare (q1, q2) = Greater
    let ( < ) q1 q2 = compare (q1, q2) = Less
    let ( >= ) q1 q2 = q1 = q2 || q1 > q2
    let ( <= ) q1 q2 = q1 = q2 || q1 < q2
    let fromInt n = Fract (Int.sign n, I.fromInt (Int.abs n), I.fromInt 1)

    let fromString str =
      let check_numerator = function
        | c :: chars' as chars -> begin
            if c = '~' then List.all Char.isDigit chars'
            else List.all Char.isDigit chars
          end
        | [] -> false
      in
      let check_denominator chars = List.all Char.isDigit chars in
      let fields = String.fields (function c -> c = '/') str in
      begin if List.length fields = 1 then
        let numerator = List.nth (fields, 0) in
        begin if check_numerator (String.explode numerator) then begin
          match I.fromString numerator with
          | Some n -> Some (Fract (I.sign n, I.abs n, I.fromInt 1))
          | _ -> None
        end
        else None
        end
      else begin
        if List.length fields = 2 then
          let numerator = List.nth (fields, 0) in
          let denominator = List.nth (fields, 1) in
          begin if
            check_numerator (String.explode numerator)
            && check_denominator (String.explode denominator)
          then begin
            match (I.fromString numerator, I.fromString denominator) with
            | Some n, Some d -> Some (normalize (Fract (I.sign n, I.abs n, d)))
            | _ -> None
          end
          else None
          end
        else None
      end
      end

    let toString (Fract (s, n, d)) =
      let nStr = I.toString (I.( * ) (I.fromInt s) n) in
      let dStr = I.toString d in
      begin if d = I.fromInt 1 then nStr else (nStr ^ "/") ^ dStr
      end

    let fromInteger n = Fract (I.sign n, I.abs n, I.fromInt 1)

    let rec floor (Fract (s, n, d) as q) =
      begin if Int.( >= ) s 0 then I.quot (n, d)
      else Integers.( ~- ) (ceiling (( ~- ) q))
      end

    and ceiling (Fract (s, n, d) as q) =
      begin if Int.( >= ) s 0 then
        I.quot (I.( + ) n (I.( - ) d (I.fromInt 1)), d)
      else Integers.( ~- ) (floor (( ~- ) q))
      end
  end

  (* Rational number:              *)
  (* q := Fract (sign, num, denom) *)
  let zero = zero
  let one = one
  let ( ~- ) = ( ~- )
  let ( + ) = ( + )
  let ( - ) = ( - )
  let ( * ) = ( * )
  let inverse = inverse
  let fromInt = fromInt
  let fromString = fromString
  let toString = toString
  let sign = sign
  let abs = abs
  let ( > ) = ( > )
  let ( < ) = ( < )
  let ( >= ) = ( >= )
  let ( <= ) = ( <= )
  let compare = compare
  let fromInteger = fromInteger
  let floor = floor
  let ceiling = ceiling
  let numerator = numerator
  let denominator = denominator
end
(* structure Rationals *)

(* # 1 "src/domains/rationals.sml.ml" *)
