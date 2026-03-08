open! Basis

(* External Syntax of Mode Declarations *)
(* Author: Carsten Schuermann *)
module type EXTMODES = sig
  module ExtSyn : EXTSYN

  (*! structure Paths : PATHS  !*)
  type nonrec mode

  val plus : Paths.region -> mode
  val star : Paths.region -> mode
  val minus : Paths.region -> mode
  val minus1 : Paths.region -> mode

  type nonrec modedec

  module Short : sig
    type nonrec mterm
    type nonrec mspine

    val mnil : Paths.region -> mspine
    val mapp : (mode * string option) * mspine -> mspine
    val mroot : string list * string * Paths.region * mspine -> mterm
    val toModedec : mterm -> modedec
  end

  module Full : sig
    type nonrec mterm

    val mroot : ExtSyn.term * Paths.region -> mterm
    val mpi : mode * ExtSyn.dec * mterm -> mterm
    val toModedec : mterm -> modedec
  end
end

(* signature EXTMODES *)
module type RECON_MODE = sig
  (*! structure ModeSyn : MODESYN !*)
  include EXTMODES

  exception Error of string

  val modeToMode : modedec -> (IntSyn.cid * ModeSyn.modeSpine_) * Paths.region
end
(* signature RECON_MODE *)
