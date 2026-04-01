(* # 1 "src/m2/skolem.sig.ml" *)
open! Basis

(* Skolem administration *)
(* Author: Carsten Schuermann *)

module type SKOLEM = sig
  (*! structure IntSyn : INTSYN !*)
  val install : IntSyn.cid list -> unit
end
