include module type of Funnames_intf

module FunNames (FunNames__0 : sig
  module Global : GLOBAL

  (*! structure FunSyn' : FUNSYN !*)
  module HashTable : TABLE with type key = string
end) : Funnames_intf.FUNNAMES
