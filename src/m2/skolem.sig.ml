open! Basis

(* Skolem administration *)
(* Author: Carsten Schuermann *)
module type SKOLEM = sig
  (*! structure IntSyn : INTSYN !*)
  val install : IntSyn.cid list -> unit
end
(* signature SKOLEM *)
