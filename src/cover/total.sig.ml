open! Basis

(* Total Declarations *)
(* Author: Frank Pfenning *)
module type TOTAL = sig
  (*! structure IntSyn : INTSYN !*)
  exception Error of string

  val reset : unit -> unit
  val install : IntSyn.cid -> unit

  (* install(a) --- a is total in its input arguments *)
  val uninstall : IntSyn.cid -> bool

  (* true: was known to be total *)
  val checkFam : IntSyn.cid -> unit
end
(* may raise Error(msg) *)
(* signature TOTAL *)
