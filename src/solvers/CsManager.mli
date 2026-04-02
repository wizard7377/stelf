include module type of CsManager_intf
include CS_MANAGER

module MakeCsManager (CSManager__0 : sig
  module Global : GLOBAL

  (*! structure IntSyn : INTSYN !*)
  module Unify : UNIFY

  (*! sharing Unify.IntSyn = IntSyn !*)
  module Fixity : FIXITY
end) : CS_MANAGER with module Fixity = CSManager__0.Fixity
