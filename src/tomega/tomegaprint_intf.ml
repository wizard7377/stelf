(* # 1 "src/tomega/tomegaprint.sig.ml" *)
open! Basis

module type TOMEGAPRINT = sig
  (*! structure IntSyn : INTSYN !*)
  (*! structure Tomega : TOMEGA  !*)
  module Formatter : FORMATTER

  exception Error of string

  val formatFor : Tomega.dec IntSyn.ctx * Tomega.for_ -> Formatter.format
  val forToString : Tomega.dec IntSyn.ctx * Tomega.for_ -> string

  val formatFun :
    (string list * Tomega.lemma list) * Tomega.prg -> Formatter.format

  val formatPrg : Tomega.dec IntSyn.ctx * Tomega.prg -> Formatter.format

  (*  val formatLemmaDec: FunSyn.LemmaDec -> Formatter.format *)
  val funToString : (string list * Tomega.lemma list) * Tomega.prg -> string

  (* funToString ((names, projs), P)  = s
     cids is the list of mututal recursive type families.  (could also be names)
     projs are the projection functions used internally,  They must be in the
     same order as names.  The nth name corresponds to the nth projection function
  *)
  val evarReset : unit -> unit
  val evarName : string -> Tomega.prg
  val nameEVar : Tomega.prg -> string
  val prgToString : Tomega.dec IntSyn.ctx * Tomega.prg -> string
  val nameCtx : Tomega.dec IntSyn.ctx -> Tomega.dec IntSyn.ctx
  val formatCtx : Tomega.dec IntSyn.ctx -> Formatter.format
  val ctxToString : Tomega.dec IntSyn.ctx -> string
end
