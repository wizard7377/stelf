include module type of Funweaken_intf

module FunWeaken (FunWeaken__0 : sig
  module Weaken : Weaken_intf.WEAKEN
end) : Funweaken_intf.FUNWEAKEN
