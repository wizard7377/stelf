open! Basis
open! Table_instances

include MakeOrigins (struct
  module Global = Global
  module Table = StringHashTable
end)
