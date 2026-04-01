(* # 1 "src/compress/compress_.sig.ml" *)
open! Basis

(** `Compressed' terms with omitted redundant arguments *)

module type COMPRESS = sig
  val sgnReset : unit -> unit
  (** type ConDec*)

  val sgnLookup : IntSyn.cid -> Sgn.sigent

  val sgnResetUpTo : int -> unit
  (** val sgnApp : (IntSyn.cid -> unit) -> unit *)

  val sgnCompressUpTo : int -> unit
  val check : Syntax.tp list * Syntax.term * Syntax.tp -> bool
  val set_modes : int * Syntax.mode list -> unit
end
