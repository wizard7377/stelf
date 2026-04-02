include module type of CsManager_intf
include CS_MANAGER

module MakeCsManager
    (Global : GLOBAL)
    (Unify : UNIFY)
    (Fixity : FIXITY) :
  CS_MANAGER with module Fixity = Fixity
(*
  (*! structure IntSyn : INTSYN !*)
  (*! sharing Unify.IntSyn = IntSyn !*)
*)
