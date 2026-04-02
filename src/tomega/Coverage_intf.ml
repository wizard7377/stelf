(* # 1 "src/tomega/Coverage.sig.ml" *)
open! Basis

module type TOMEGACOVERAGE = sig
  (*! structure IntSyn : INTSYN !*)
  (*! structure Tomega : TOMEGA !*)
  exception Error of string

  val coverageCheckPrg :
    Tomega.worlds * Tomega.dec IntSyn.ctx * Tomega.prg -> unit
end
