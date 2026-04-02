(* # 1 "src/domains/Integers.sig.ml" *)

open Basis

(* Integers *)
(* Author: Roberto Virga *)

module type INTEGERS = sig
  include INTEGER

  val gcd : int * int -> int
  val lcm : int * int -> int
  val solve_gcd : int * int -> int * int
end
