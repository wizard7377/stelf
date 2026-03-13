(* # 1 "src/domains/ordered_field.sig.ml" *)
open! Basis
open Field

(* Ordered Field *)
(* Author: Roberto Virga *)
module type ORDERED_FIELD = sig
  include FIELD

  (* Sign operations *)
  val sign : number -> int
  val abs : number -> number

  (* Comparisons predicates *)
  val ( > ) : number -> number -> bool
  val ( < ) : number -> number -> bool
  val ( >= ) : number -> number -> bool
  val ( <= ) : number -> number -> bool
  val compare : number * number -> order
end
(* signature ORDERED_FIELD *)

(* # 1 "src/domains/ordered_field.fun.ml" *)

(* # 1 "src/domains/ordered_field.sml.ml" *)
