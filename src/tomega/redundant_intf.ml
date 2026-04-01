(* # 1 "src/tomega/redundant.sig.ml" *)
open! Basis

module type REDUNDANT = sig
  exception Error of string

  val convert : Tomega.prg -> Tomega.prg
end
