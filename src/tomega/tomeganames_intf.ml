(* # 1 "src/tomega/tomeganames.sig.ml" *)
open! Basis

module type TOMEGANAMES = sig
  val decName : Tomega.dec IntSyn.ctx * Tomega.dec -> Tomega.dec
end
