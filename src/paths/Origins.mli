include module type of Origins_intf

module MakeOrigins (Global : GLOBAL) (Table : TABLE with type key = string) : ORIGINS

module Origins : ORIGINS
include ORIGINS
