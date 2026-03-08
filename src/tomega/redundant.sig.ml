open! Basis

module type REDUNDANT = sig
  exception Error of string

  val convert : Tomega.prg_ -> Tomega.prg_
end
