open! Basis
module Tomega = Lambda_.Tomega

module type REDUNDANT = sig
  exception Error of string

  val convert : Tomega.prg_ -> Tomega.prg_
end
