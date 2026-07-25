(* # 1 "src/tomega/Converter.sig.ml" *)
open! Basis

module type CONVERTER = sig
  (*! structure IntSyn : INTSYN !*)
  (*! structure Tomega : TOMEGA !*)
  exception Error of string
  exception Error' of Tomega.sub

  val convertFor : IntSyn.cid list -> Tomega.for_
  val convertPrg : IntSyn.cid list -> Tomega.prg

  val installPrg :
    IntSyn.cid list ->
    IntSyn.cid * Tomega.lemma list * Tomega.lemma list (* projections *)

  (* selections *)
  val convertGoal : Tomega.dec IntSyn.ctx * IntSyn.exp -> Tomega.prg
end
