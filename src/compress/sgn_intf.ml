(* # 1 "src/compress/sgn.sig.ml" *)

(* # 1 "src/compress/sgn.fun.ml" *)

(* # 1 "src/compress/sgn.sml.ml" *)
open! Syntax
open! Basis

module type SGN = sig
  type sigent
  type def = Def_none | Def_term of Syntax.term | Def_type of Syntax.tp

  val condec : string * Syntax.tp * Syntax.tp -> sigent
  val tycondec : string * Syntax.knd * Syntax.knd -> sigent

  val defn :
    string * Syntax.tp * Syntax.tp * Syntax.term * Syntax.term -> sigent

  val tydefn :
    string * Syntax.knd * Syntax.knd * Syntax.tp * Syntax.tp -> sigent

  val abbrev :
    string * Syntax.tp * Syntax.tp * Syntax.term * Syntax.term -> sigent

  val tyabbrev :
    string * Syntax.knd * Syntax.knd * Syntax.tp * Syntax.tp -> sigent

  val typeOfSigent : sigent -> Syntax.tp
  val classifier : int -> Syntax.class_
  val o_classifier : int -> Syntax.class_
  val def : int -> def
  val o_def : int -> def
  val update : int * sigent -> unit
  val sub : int -> sigent option
  val clear : unit -> unit
  val get_modes : int -> Syntax.mode list option
  val set_modes : int * Syntax.mode list -> unit
  val get_p : int -> bool option
  val set_p : int * bool -> unit
  val abbreviation : int -> bool
end
