(* # 1 "src/domains/OrderedField.sig.ml" *)
open Basis
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
