include module type of Modsyn_intf

module ModSyn (ModSyn__0 : sig
  (* Syntax for elaborated modules *)
  (* Author: Kevin Watkins *)
  module Global : GLOBAL

  (*! structure IntSyn' : INTSYN !*)
  module Names__ : NAMES

  (*! sharing Names'.IntSyn = IntSyn' !*)
  (*! structure Paths' : PATHS !*)
  module Origins : Origins.ORIGINS

  (*! sharing Origins.Paths = Paths' !*)
  module Whnf : WHNF

  (*! sharing Whnf.IntSyn = IntSyn' !*)
  module Strict : Typecheck_.STRICT

  (*! sharing Strict.IntSyn = IntSyn' !*)
  module IntTree : TABLE with type key = int
  module HashTable : TABLE with type key = string
end) : MODSYN
