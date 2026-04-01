include module type of Origins_intf

module MakeOrigins (Origins__0 : sig
  module Global : GLOBAL
  module Table : TABLE with type key = string
end) : ORIGINS

module Origins : ORIGINS
include ORIGINS
