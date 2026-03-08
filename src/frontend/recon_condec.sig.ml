open! Basis

(* External Syntax for signature entries *)
(* Author: Frank Pfenning *)
module type EXTCONDEC = sig
  module ExtSyn : EXTSYN

  (*! structure Paths : PATHS !*)
  type nonrec condec

  (* constant declaration *)
  val condec : string * ExtSyn.term -> condec

  (* id : tm *)
  val blockdec : string * ExtSyn.dec list * ExtSyn.dec list -> condec
  val blockdef : string * (string list * string) list -> condec
  val condef : string option * ExtSyn.term * ExtSyn.term option -> condec
end

(* id : tm = tm | _ : tm = tm *)
(* signature EXTCONDEC *)
module type RECON_CONDEC = sig
  (*! structure IntSyn : INTSYN !*)
  include EXTCONDEC

  exception Error of string

  val condecToConDec :
    condec * Paths.location * bool ->
    IntSyn.conDec_ option * Paths.occConDec option

  (* optional ConDec is absent for anonymous definitions *)
  (* bool = true means that condec is an abbreviation *)
  val internalInst :
    IntSyn.conDec_ * IntSyn.conDec_ * Paths.region -> IntSyn.conDec_

  val externalInst :
    IntSyn.conDec_ * ExtSyn.term * Paths.region -> IntSyn.conDec_
end
(* signature RECON_CONDEC *)
