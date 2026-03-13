(* # 1 "src/m2/qed.sig.ml" *)
open! Basis
open Metasyn

(* Qed *)
(* Author: Carsten Schuermann *)
module type QED = sig
  module MetaSyn : METASYN

  exception Error of string

  val subgoal : MetaSyn.state_ -> bool
end
(* signature QED *)

(* # 1 "src/m2/qed.fun.ml" *)
open! Basis
open Metasyn

(* QED *)
(* Author: Carsten Schuermann *)
module Qed (Qed__0 : sig
  module Global : GLOBAL
  module MetaSyn' : METASYN
end) : QED with module MetaSyn = Qed__0.MetaSyn' = struct
  open Qed__0
  module MetaSyn = MetaSyn'

  exception Error of string

  open! struct
    module M = MetaSyn
    module I = IntSyn

    let rec subgoal (M.State (name, M.Prefix (g_, m_, b_), v_)) =
      let rec check = function
        | null_ -> true
        | I.Decl (m_, top_) -> check m_
        | I.Decl (m_, bot_) -> false
      in
      check m_
  end

  let subgoal = subgoal
end
(* local *)
(* functor Qed *)

(* # 1 "src/m2/qed.sml.ml" *)
