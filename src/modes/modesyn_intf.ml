(* # 1 "src/modes/modesyn.sig.ml" *)

(* # 1 "src/modes/modesyn.fun.ml" *)

(* # 1 "src/modes/modesyn.sml.ml" *)
open! Basis

(* Mode Syntax *)
(* Author: Carsten Schuermann *)
(* Modified: Frank Pfenning, Roberto Virga *)

module type MODESYN = sig
  (*! structure IntSyn : INTSYN !*)
  type mode = Plus | Star | Minus | Minus1 [@@deriving eq, ord, show]

  type modeSpine = Mnil | Mapp of marg * modeSpine
  and marg = Marg of mode * string option [@@deriving eq, ord, show]

  val modeEqual : mode * mode -> bool
  val modeToString : mode -> string
end
