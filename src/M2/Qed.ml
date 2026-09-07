open! Global.Global_
open! Intsyn.Lambda_

(* # 1 "src/m2/Qed.sig.ml" *)
open Metasyn

(* Qed *)
(* Author: Carsten Schuermann *)
include QED
(* signature QED *)

(* # 1 "src/m2/Qed.fun.ml" *)
open! Basis
open Metasyn

(* QED *)
(* Author: Carsten Schuermann *)

exception Error of string

let () =
  Printexc.register_printer (function Error msg -> Some msg | _ -> None)

module Qed (Qed__0 : sig
  module Global : GLOBAL
  module MetaSyn' : Metasyn.METASYN
end) : QED with module MetaSyn = Qed__0.MetaSyn' = struct
  open Qed__0
  module MetaSyn = MetaSyn'

  exception Error = Error

  open! struct
    module M = MetaSyn
    module I = IntSyn

    let subgoal (M.State (name, M.Prefix (g, m, b), v)) =
      let rec check = function
        | I.Null -> true
        | I.Decl (m, M.Top) -> check m
        | I.Decl (m, M.Bot) -> false
      in
      check m
  end

  let subgoal = subgoal
end
(* local *)
(* functor Qed *)

(* # 1 "src/m2/Qed.sml.ml" *)
