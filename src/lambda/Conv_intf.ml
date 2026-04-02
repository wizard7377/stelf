(* # 1 "src/lambda/Conv.sig.ml" *)
open! Basis
(** Definitional convertibility modulo beta/eta. *)

open Intsyn

(* Convertibility Modulo Beta and Eta *)
(* Author: Frank Pfenning, Carsten Schuermann *)

module type CONV = sig
  (*! structure IntSyn : INTSYN !*)
  val conv : IntSyn.eclo * IntSyn.eclo -> bool
  val conv_dec : (IntSyn.dec * IntSyn.sub) * (IntSyn.dec * IntSyn.sub) -> bool
  val conv_sub : IntSyn.sub * IntSyn.sub -> bool

  val convDec : (IntSyn.dec * IntSyn.sub) * (IntSyn.dec * IntSyn.sub) -> bool
  (** Compatibility alias for {!conv_dec}. *)

  val convSub : IntSyn.sub * IntSyn.sub -> bool
  (** Compatibility alias for {!conv_sub}. *)
end
