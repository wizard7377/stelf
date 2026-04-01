(* # 1 "src/paths/origins.sig.ml" *)
open! Basis
open Paths_

module type ORIGINS = sig
  (*! structure IntSyn : INTSYN !*)
  (*! structure Paths : PATHS !*)
  val reset : unit -> unit
  val installLinesInfo : string * Paths_.Paths.linesInfo -> unit
  val linesInfoLookup : string -> Paths_.Paths.linesInfo option
  val installOrigin : IntSyn.cid * (string * Paths_.Paths.occConDec option) -> unit
  val originLookup : IntSyn.cid -> string * Paths_.Paths.occConDec option
end
