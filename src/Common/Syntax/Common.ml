(** Abstract type for position/metadata tags attached to expressions. *)
module type TAG = sig
  type t
end

(* TODO Replace with IDX name *)
module type CID = sig
  type t

  val equal : t -> t -> bool
  val compare : t -> t -> int
  val pp : Format.formatter -> t -> unit
  val show : t -> string
  val fresh : unit -> t
  val reset : unit -> unit
end

module type COMMON = sig
  module Tag : TAG
  module Cid : CID
  module Mid : CID
  module Global : Global.GLOBAL.GLOBAL
end
