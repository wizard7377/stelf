open! Intsyn.Lambda_

(* # 1 "src/tomega/Tomeganames.sig.ml" *)

module type TOMEGANAMES = sig
  val decName : Tomega.dec IntSyn.ctx -> Tomega.dec -> Tomega.dec
end
