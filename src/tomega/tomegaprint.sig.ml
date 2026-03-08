open! Basis

(* Printing of functional proof terms *)
(* Author: Carsten Schuermann *)
module type TOMEGAPRINT = sig
  (*! structure IntSyn : INTSYN !*)
  (*! structure Tomega : TOMEGA  !*)
  module Formatter : FORMATTER

  exception Error of string

  val formatFor : Tomega.dec_ IntSyn.ctx_ * Tomega.for_ -> Formatter.format
  val forToString : Tomega.dec_ IntSyn.ctx_ * Tomega.for_ -> string

  val formatFun :
    (string list * Tomega.lemma list) * Tomega.prg_ -> Formatter.format

  val formatPrg : Tomega.dec_ IntSyn.ctx_ * Tomega.prg_ -> Formatter.format

  (*  val formatLemmaDec: FunSyn.LemmaDec -> Formatter.format *)
  val funToString : (string list * Tomega.lemma list) * Tomega.prg_ -> string

  (* funToString ((names, projs), P)  = s
     cids is the list of mututal recursive type families.  (could also be names)
     projs are the projection functions used internally,  They must be in the
     same order as names.  The nth name corresponds to the nth projection function
  *)
  val evarReset : unit -> unit
  val evarName : string -> Tomega.prg_
  val nameEVar : Tomega.prg_ -> string
  val prgToString : Tomega.dec_ IntSyn.ctx_ * Tomega.prg_ -> string
  val nameCtx : Tomega.dec_ IntSyn.ctx_ -> Tomega.dec_ IntSyn.ctx_
  val formatCtx : Tomega.dec_ IntSyn.ctx_ -> Formatter.format
  val ctxToString : Tomega.dec_ IntSyn.ctx_ -> string
end
(*  val lemmaDecToString : FunSyn.LemmaDec -> string *)
(* signature TOMEGAPRINT *)
