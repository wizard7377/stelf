(* Shared term-building helpers for IntSyn unit tests.
   All helpers produce closed, substitution-free terms using only de Bruijn
   variables (BVar) and the Uni/Pi/Lam/Root constructors — no global
   signature lookups, so tests run without any signature state. *)

open Intsyn.IntSyn

let id_sub = Shift 0
let null_ctx = Null

(* bvar n — de Bruijn variable n as a closed expression *)
let bvar n = Root (BVar n, Nil)

(* lam_ d body — lambda abstraction (Dec with no name) *)
let lam_ ty body = Lam (Dec (None, ty), body)

(* Alcotest testable for exp based on structural equality.
   show_exp returns "<exp>" for all values which is uninformative but works. *)
let exp_testable =
  Alcotest.testable
    (fun fmt _ -> Format.pp_print_string fmt "<exp>")
    equal_exp

