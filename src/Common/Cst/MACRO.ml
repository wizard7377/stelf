module type MACRO = sig
  module C : CST.CST

  type t

  val args : t -> int
  val create : int -> C.cmd -> t
  val apply : t -> C.term list -> C.cmd
  val reify : t -> C.cmd
end
