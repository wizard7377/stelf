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

(* signature MODESYN *)
module ModeSyn : MODESYN = struct
  exception Error of string

  type mode = Plus | Star | Minus | Minus1 [@@deriving eq, ord, show]

  type modeSpine = Mnil | Mapp of marg * modeSpine
  and marg = Marg of mode * string option [@@deriving eq, ord, show]

  (* modeEqual (M1, M2) = true iff M1 = M2 *)
  let rec modeEqual = function
    | Plus, Plus -> true
    | Star, Star -> true
    | Minus, Minus -> true
    | Minus1, Minus1 -> true
    | _, _ -> false

  (* modeToString M = string
    
       converts a mode into a string for error messages
  *)
  let rec modeToString = function
    | Plus -> "input (+)"
    | Star -> {|unrestricted (*)|}
    | Minus -> "output (-)"
    | Minus1 -> "unique output (-1)"
end
(* structure ModeSyn *)
