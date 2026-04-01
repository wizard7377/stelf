(* # 1 "src/cover/total.sig.ml" *)
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

module type COVER = sig
  exception Error of string

  val checkNoDef : IntSyn.cid -> unit
  val checkOut : IntSyn.dctx * IntSyn.eclo -> unit
  val checkCovers : IntSyn.cid * Modesyn.ModeSyn.modeSpine -> unit

  val coverageCheckCases :
    Tomega.worlds * (IntSyn.dctx * IntSyn.sub) list * IntSyn.dctx -> unit
end
