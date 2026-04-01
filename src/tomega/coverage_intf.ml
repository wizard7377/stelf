(* # 1 "src/tomega/coverage.sig.ml" *)
open! Basis

module type TOMEGACOVERAGE = sig
  (*! structure IntSyn : INTSYN !*)
  (*! structure Tomega : TOMEGA !*)
  exception Error of string

  val coverageCheckPrg :
    Tomega.worlds * Tomega.dec IntSyn.ctx * Tomega.prg -> unit
end
