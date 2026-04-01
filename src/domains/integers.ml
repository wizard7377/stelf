(* # 1 "src/domains/integers.sig.ml" *)

open Basis

(* Integers *)
(* Author: Roberto Virga *)
include Integers_intf
(* signature INTEGERS *)

(* # 1 "src/domains/integers.fun.ml" *)

(* Rationals *)
(* Author: Roberto Virga *)
module Integers (Integer : INTEGER) : INTEGERS = struct
  include Integer

  let zero = fromInt 0
  let one = fromInt 1

  let solve_gcd (m, n) =
    let rec solve' (m, n) =
      let q = quot (m, n) in
      let r = rem (m, n) in
      begin if r = zero then (zero, one)
      else
        let x, y = solve' (n, r) in
        (y, x - (q * y))
      end
    in
    let am = abs m in
    let an = abs n in
    let sm = fromInt (sign m) in
    let sn = fromInt (sign n) in
    begin if am > an then
      (function x, y -> (sm * x, sn * y)) (solve' (am, an))
    else (function x, y -> (sm * y, sn * x)) (solve' (an, am))
    end

  let gcd (m, n) =
    let x, y = solve_gcd (m, n) in
    (m * x) + (n * y)

  let lcm (m, n) = quot (m * n, gcd (m, n))

  let fromString str =
    let check = function
      | c :: chars' as chars -> begin
          if c = '~' then List.all Char.isDigit chars'
          else List.all Char.isDigit chars
        end
      | [] -> false
    in
    begin if check (String.explode str) then Integer.fromString str else None
    end
end
(* structure Integers *)

(* # 1 "src/domains/integers.sml.ml" *)
